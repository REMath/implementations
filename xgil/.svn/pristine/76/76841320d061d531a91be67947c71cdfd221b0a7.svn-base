
// Sixgill: Static assertion checker for C/C++ programs.
// Copyright (C) 2009-2010  Stanford University
// Author: Brian Hackett
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <stdio.h>
#include <errno.h>
#include <time.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <signal.h>

#include <libevent/event.h>

#include <util/config.h>
#include <util/monitor.h>
#include <backend/backend_block.h>
#include <imlang/storage.h>
#include <memory/mstorage.h>

NAMESPACE_XGILL_USING

const char *USAGE = "xmanager [options]";

ConfigOption spawn_command(CK_String, "spawn-command", "",
  "Command to spawn worker processes. -remote=... will be appended");

ConfigOption spawn_count(CK_UInt, "spawn-count", "0",
  "Number of worker processes to spawn");

ConfigOption terminate_on_assert(CK_Flag, "terminate-on-assert", NULL,
  "die instead of pausing when assertion is hit");

// whether we are currently handling an incoming transaction.
bool handling_transaction = false;

// file descriptor for the socket the server is listening on.
int server_socket = 0;

// handler if we get a SIGTERM/SIGINT. make sure to clean up properly from
// these and treat as normal termination.
static void termination_handler(int signal)
{
  // can't normally terminate in the middle of handling a transaction.
  if (handling_transaction) {
    logout << "ERROR: Signal received while handling transaction, aborting..."
           << endl << flush;
    abort();
  }

  // ignore multiple signals.
  static bool terminating = false;
  if (terminating) return;
  terminating = true;

  logout << "Termination signal received, finishing..." << endl << flush;
  close(server_socket);

  ClearBlockCaches();
  ClearMemoryCaches();
  AnalysisFinish(0);
}

// number of initial/final transactions we have heard. 0 if we are going
// to run until we receive a SIGINT, otherwise we will run until we
// have heard as many final as initial transactions.
size_t received_initial = 0;
size_t received_final = 0;

// event for incoming connections
struct event connect_event;

// per-connection data
struct ConnectData {
  // whether this is a live connection.
  bool live;

  // buffer containing partially/fully read packet
  Buffer read_buf;

  // buffer containing partially/fully written packet.
  // this does not have its own allocation but refers to
  // data in read_buf; there will not be simultaneous
  // reading and writing.
  Buffer write_buf;

  // event associated with this connection
  struct event ev;

  // file descriptor associated with this connection
  int fd;

  ConnectData()
    : live(false), read_buf(), write_buf(NULL, 0), fd(-1)
  {}
};

// all active connections
Vector<ConnectData*> connections;

void handle_event(int fd, short, void *v)
{
  bool success;

  size_t index = (size_t) v;
  Assert(index < connections.Size());

  ConnectData *cdata = connections[index];
  Assert(cdata->live);

  if (cdata->write_buf.size != 0) {
    success = WritePacket(fd, &cdata->write_buf);
    if (success) {
      cdata->write_buf.base = NULL;
      cdata->write_buf.pos = NULL;
      cdata->write_buf.size = 0;
    }
  }
  else {
    size_t length = cdata->read_buf.pos - cdata->read_buf.base;

    success = ReadPacket(fd, &cdata->read_buf);
    if (success) {
      size_t data_length =
        cdata->read_buf.pos - cdata->read_buf.base - UINT32_LENGTH;
      Buffer transaction_buf(cdata->read_buf.base + UINT32_LENGTH,
                             data_length);

      Transaction *t = new Transaction();
      if (!t->Read(&transaction_buf)) {
        logout << "ERROR: Corrupt packet data" << endl;
        delete t;
        return;
      }

      handling_transaction = true;
      t->Execute();

      cdata->read_buf.pos = cdata->read_buf.base;
      cdata->read_buf.Ensure(UINT32_LENGTH);
      cdata->read_buf.pos += UINT32_LENGTH;
      t->WriteResult(&cdata->read_buf);

      cdata->write_buf.base = cdata->read_buf.base;
      cdata->write_buf.pos = cdata->write_buf.base;
      cdata->write_buf.size = cdata->read_buf.pos - cdata->read_buf.base;

      cdata->read_buf.pos = cdata->read_buf.base;

      success = WritePacket(fd, &cdata->write_buf);
      if (success) {
        cdata->write_buf.base = NULL;
        cdata->write_buf.pos = NULL;
        cdata->write_buf.size = 0;
      }

      // watch for initial and final transactions.

      if (t->IsInitial()) {
        Assert(!spawn_count.IsSpecified());
        received_initial++;
      }

      if (t->IsFinal()) {
        Assert(received_final < received_initial);
        received_final++;
        if (received_final == received_initial) {
          // this was the last client, so cleanup and exit.
          logout << "Final transaction received, finishing..."
                 << endl << flush;
          close(server_socket);

          ClearBlockCaches();
          ClearMemoryCaches();
          AnalysisFinish(0);
        }
      }

      delete t;
      handling_transaction = false;
    }
    else if ((ssize_t) length == cdata->read_buf.pos - cdata->read_buf.base) {
      // connection is closed. there is nothing to read so remove the event.
      event_del(&cdata->ev);
      close(cdata->fd);

      cdata->live = false;
      cdata->read_buf.Reset(0);
      cdata->write_buf.Reset(0);
    }
  }
}

void handle_connect(int sockfd, short, void*)
{
  logout << "Received connection." << endl << flush;

  int newfd = accept(sockfd, NULL, 0);
  if (newfd == -1) {
    logout << "ERROR: accept() failure: " << errno << endl;
    return;
  }

  ConnectData *cdata = new ConnectData();
  connections.PushBack(cdata);

  cdata->live = true;
  cdata->fd = newfd;
  event_set(&cdata->ev, newfd, EV_READ | EV_PERSIST,
            handle_event, (void*) (connections.Size() - 1));

  int ret = event_add(&cdata->ev, NULL);
  if (ret == -1) {
    logout << "ERROR: event_add() failure: " << errno << endl;
    delete cdata;
    return;
  }
}

// get the IP address and port for a server socket on the current
// machine. there is probably a simpler way of doing this.
bool GetCurrentHost(int sockfd,
                    char *host, size_t hostlen, unsigned short *port)
{
  int ret;

  // get the DNS name for the current host
  char hostname[256];
  ret = gethostname(hostname, 256);
  if (ret == -1) {
    logout << "ERROR: gethostname() failure: " << errno << endl;
    return false;
  }

  bool found_host = false;

  // try to find the IP address corresponding to that current host
  struct hostent* ent = gethostbyname(hostname);
  if (ent != NULL && ent->h_addr_list && ent->h_length == 4) {
    char **phost = ent->h_addr_list;
    while (*phost) {
      const char *xhost = inet_ntop(PF_INET, *phost, host, hostlen);
      if (xhost != NULL) {
        found_host = true;
        break;
      }
      phost++;
    }
  }

  if (!found_host) {
    logout << "ERROR: could not determine listening host." << endl;
    return false;
  }

  struct sockaddr_in use_addr;
  memset(&use_addr, 0, sizeof(use_addr));

  socklen_t use_len = sizeof(use_addr);
  ret = getsockname(sockfd, (sockaddr*) &use_addr, &use_len);
  if (ret == -1) {
    logout << "ERROR: getsockname() failure: " << errno << endl;
    return false;
  }

  if (use_addr.sin_port == 0) {
    logout << "ERROR: could not determine listening port." << endl;
    return false;
  }

  *port = ntohs(use_addr.sin_port);
  return true;
}

int main(int argc, const char **argv)
{
  spawn_command.Enable();
  spawn_count.Enable();
  terminate_on_assert.Enable();

#ifdef USE_COUNT_ALLOCATOR
  memory_limit.Enable();
#endif

  modset_wait.Enable();

  Vector<const char*> unspecified;
  bool parsed = Config::Parse(argc, argv, &unspecified);
  if (!parsed || !unspecified.Empty()) {
    Config::PrintUsage(USAGE);
    return 1;
  }

  AnalysisPrepare();

  // use a different handler for termination signals.
  signal(SIGINT, termination_handler);
  signal(SIGTERM, termination_handler);

  // xmanager failures are unrecoverable.
  g_pause_assertions = true;
  if (terminate_on_assert.IsSpecified()) {
    g_pause_assertions = false;
  }

  int ret;

  event_init();

  server_socket = socket(PF_INET, SOCK_STREAM, 0);
  if (server_socket == -1) {
    logout << "ERROR: socket() failure: " << errno << endl;
    return 1;
  }

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));

  ret = bind(server_socket, (sockaddr*) &addr, sizeof(addr));
  if (ret == -1) {
    logout << "ERROR: bind() failure: " << errno << endl;
    return 1;
  }

  int optval = 1;
  ret = setsockopt(server_socket, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval));
  if (ret == -1) {
    logout << "ERROR: setsockopt() failure: " << errno << endl;
    return 1;
  }

  int oldcode = fcntl(server_socket, F_GETFL, 0);
  if (oldcode == -1) {
    logout << "ERROR: fcntl() failure: " << errno << endl;
    return 1;
  }

  ret = fcntl(server_socket, F_SETFL, oldcode | O_NONBLOCK);
  if (ret == -1) {
    logout << "ERROR: fcntl() failure: " << errno << endl;
    return 1;
  }

  ret = listen(server_socket, 200);
  if (ret == -1) {
    logout << "ERROR: listen() failure: " << errno << endl;
    return 1;
  }

  event_set(&connect_event, server_socket, EV_READ | EV_PERSIST,
            handle_connect, NULL);

  ret = event_add(&connect_event, NULL);
  if (ret == -1) {
    logout << "ERROR: event_add() failure: " << errno << endl;
    return 1;
  }

  char hostbuf[256];
  unsigned short port;

  bool hostret = GetCurrentHost(server_socket, hostbuf, sizeof(hostbuf), &port);
  if (!hostret)
    return 1;

  logout << "Listening on " << hostbuf << ":" << port << endl << flush;

  // spawn the child processes if needed. this is done with a system()
  // call, in the expectation the call will either fork a new process
  // on this machine, or start up a process on another machine.
  if (spawn_count.IsSpecified()) {
    if (!spawn_command.IsSpecified()) {
      logout << "ERROR: -spawn-count must be used with -spawn-command" << endl;
      Config::PrintUsage(USAGE);
      return 1;
    }

    Buffer command_buf;
    BufferOutStream out(&command_buf);
    out << spawn_command.StringValue()
        << " -remote=" << hostbuf << ":" << port << '\0';
    const char *command = (const char*) command_buf.base;

    for (size_t ind = 0; ind < spawn_count.UIntValue(); ind++) {
      int ret = system(command);
      if (ret != 0) {
        logout << "ERROR: Spawn command failed: " << command << endl;
        return 1;
      }
      else {
        logout << "Command process spawned" << endl;
      }
      // we will not receive an initial transaction from these workers.
      received_initial++;
    }
  }

  ret = event_dispatch();

  if (ret == -1) {
    logout << "ERROR: event_dispatch() failure: " << errno << endl;
    return 1;
  }

  Assert(false);
}
