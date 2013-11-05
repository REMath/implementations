
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

#include <sys/socket.h>
#include <unistd.h>
#include <errno.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <signal.h>

#include "transaction.h"
#include "operand.h"
#include "action.h"
#include "backend.h"
#include "serial.h"
#include <util/config.h>

NAMESPACE_XGILL_BEGIN

/////////////////////////////////////////////////////////////////////
// Transaction
/////////////////////////////////////////////////////////////////////

Transaction::Transaction()
{
  // Clear() does not depend on non-list members being initialized
  Clear();
}

Transaction::~Transaction()
{
  Clear();
}

void Transaction::PushAction(TAction *a)
{
  Assert(!m_has_executed);
  m_actions.PushBack(a);
}

size_t Transaction::GetActionCount()
{
  Assert(!m_has_executed);
  return m_actions.Size();
}

void Transaction::SetInitial()
{
  Assert(!m_has_executed);
  m_initial = true;
}

void Transaction::SetFinal()
{
  Assert(!m_has_executed);
  m_final = true;
}

void Transaction::Execute()
{
  Assert(!m_has_executed);
  m_has_executed = true;

  static bool g_backend_started = false;

  if (!g_backend_started) {
    TransactionBackend::StartBackend();
    g_backend_started = true;
  }

  m_success = true;

  // execute each of the main actions in order.
  for (size_t ind = 0; ind < m_actions.Size(); ind++) {
    TAction *a = m_actions[ind];
    m_success = a->Execute();
    if (!m_success)
      break;
  }
}

bool Transaction::HasExecuted() const
{
  return m_has_executed;
}

bool Transaction::HasSuccess() const
{
  Assert(m_has_executed);
  return m_success;
}

bool Transaction::IsInitial() const
{
  Assert(m_has_executed);
  return m_initial;
}

bool Transaction::IsFinal() const
{
  Assert(m_has_executed);
  return m_final;
}

void Transaction::Print() const
{
  if (!m_actions.Empty()) {
    for (size_t ind = 0; ind < m_actions.Size(); ind++)
      m_actions[ind]->Print(logout, 0);
  }
  else {
    logout << "[empty transaction]" << endl;
  }
}

void Transaction::Write(Buffer *buf) const
{
  Assert(!m_has_executed);

  WriteOpenTag(buf, TAG_Transaction);
  for (size_t ind = 0; ind < m_actions.Size(); ind++)
    TAction::Write(buf, m_actions[ind]);
  if (m_initial)
    WriteTagEmpty(buf, TAG_TransactionInitial);
  if (m_final)
    WriteTagEmpty(buf, TAG_TransactionFinal);
  for (size_t ind = 0; ind < m_variables.Size(); ind++) {
    if (m_variables[ind].is_return) {
      WriteOpenTag(buf, TAG_TransactionVariable);
      WriteTagUInt32(buf, TAG_Index, ind);
      WriteCloseTag(buf, TAG_TransactionVariable);
    }
  }
  WriteCloseTag(buf, TAG_Transaction);
}

bool Transaction::Read(Buffer *buf)
{
  Assert(!m_has_executed);
  Assert(m_actions.Empty());

  Try(ReadOpenTag(buf, TAG_Transaction));
  while (!ReadCloseTag(buf, TAG_Transaction)) {
    switch (PeekOpenTag(buf)) {
    case TAG_TAction: {
      TAction *a = TAction::Read(buf, this);
      m_actions.PushBack(a);
      break;
    }
    case TAG_TransactionInitial: {
      Try(ReadTagEmpty(buf, TAG_TransactionInitial));
      m_initial = true;
      break;
    }
    case TAG_TransactionFinal: {
      Try(ReadTagEmpty(buf, TAG_TransactionFinal));
      m_final = true;
      break;
    }
    case TAG_TransactionVariable: {
      Try(ReadOpenTag(buf, TAG_TransactionVariable));
      uint32_t index;
      Try(ReadTagUInt32(buf, TAG_Index, &index));
      Try(ReadCloseTag(buf, TAG_TransactionVariable));

      if (m_variables.Size() <= index)
        m_variables.Resize(index + 1);
      m_variables[index].is_return = true;
      break;
    }
    default:
      Try(false);
    }
  }

  return true;
}

void Transaction::WriteResult(Buffer *buf) const
{
  Assert(m_has_executed);

  WriteOpenTag(buf, TAG_TransactionResult);
  WriteTagEmpty(buf, m_success ? TAG_True : TAG_False);

  for (size_t vind = 0; vind < m_variables.Size(); vind++) {
    if (m_variables[vind].value != NULL) {
      Assert(vind != 0);
      WriteOpenTag(buf, TAG_TransactionVariable);
      WriteTagUInt32(buf, TAG_Index, vind);
      TOperand::Write(buf, m_variables[vind].value);
      WriteCloseTag(buf, TAG_TransactionVariable);
    }
  }

  WriteCloseTag(buf, TAG_TransactionResult);
}

bool Transaction::ReadResult(Buffer *buf)
{
  Assert(!m_has_executed);

  bool is_true = false;
  bool is_false = false;

  Try(ReadOpenTag(buf, TAG_TransactionResult));
  while (!ReadCloseTag(buf, TAG_TransactionResult)) {
    switch (PeekOpenTag(buf)) {
    case TAG_True: {
      Try(!is_true && !is_false);
      Try(ReadTagEmpty(buf, TAG_True));
      is_true = true;
      break;
    }
    case TAG_False: {
      Try(!is_true && !is_false);
      Try(ReadTagEmpty(buf, TAG_False));
      is_false = true;
      break;
    }
    case TAG_TransactionVariable: {
      Try(ReadOpenTag(buf, TAG_TransactionVariable));
      uint32_t index;
      Try(ReadTagUInt32(buf, TAG_Index, &index));
      TOperand *value = TOperand::Read(buf, this);
      Try(ReadCloseTag(buf, TAG_TransactionVariable));

      Assign(index, value);
      break;
    }
    default:
      Try(false);
    }
  }

  Try(is_true || is_false);

  m_success = is_true;
  m_has_executed = true;
  return true;
}

void Transaction::AddOperand(TOperand *o)
{
  m_owned_operands.PushBack(o);
}

void Transaction::AddAction(TAction *a)
{
  m_owned_actions.PushBack(a);
}

void Transaction::AddBuffer(Buffer *b)
{
  m_owned_buffers.PushBack(b);
}

const char* Transaction::CloneString(const char *str)
{
  size_t len = strlen(str) + 1;
  Buffer *b = new Buffer(len);
  memcpy(b->base, str, len);
  m_owned_buffers.PushBack(b);
  return (const char*) b->base;
}

void Transaction::Clear()
{
  m_initial = false;
  m_final = false;
  m_has_executed = false;
  m_success = false;

  // don't have to delete these guys because they are included
  // in m_owned_actions.
  m_actions.Clear();

  for (size_t oind = 0; oind < m_owned_operands.Size(); oind++)
    delete m_owned_operands[oind];

  for (size_t aind = 0; aind < m_owned_actions.Size(); aind++)
    delete m_owned_actions[aind];

  for (size_t bind = 0; bind < m_owned_buffers.Size(); bind++)
    delete m_owned_buffers[bind];

  m_owned_operands.Clear();
  m_owned_actions.Clear();
  m_owned_buffers.Clear();

  // clear variables and reserve unused space for index 0.
  m_variables.Clear();
  m_variables.PushBack(VariableInfo());
}

size_t Transaction::MakeVariable(bool is_return)
{
  m_variables.PushBack(VariableInfo());
  m_variables.Back().is_return = is_return;
  return m_variables.Size() - 1;
}

void Transaction::Assign(size_t var, TOperand *value)
{
  Assert(var != 0);
  Assert(value);
  Assert(value->Kind() != TO_Variable);

  if (var >= m_variables.Size())
    m_variables.Resize(var + 1);
  m_variables[var].value = value;
}

TOperand* Transaction::Lookup(size_t var, bool required)
{
  Assert(var != 0);
  TOperand *res = NULL;
  if (var < m_variables.Size())
    res = m_variables[var].value;
  if (required)
    Assert(res);
  return res;
}

TOperandList* Transaction::LookupList(size_t var, bool required)
{
  TOperand *res = Lookup(var, required);
  return res ? res->AsList() : NULL;
}

TOperandString* Transaction::LookupString(size_t var, bool required)
{
  TOperand *res = Lookup(var, required);
  return res ? res->AsString() : NULL;
}

TOperandBoolean* Transaction::LookupBoolean(size_t var, bool required)
{
  TOperand *res = Lookup(var, required);
  return res ? res->AsBoolean() : NULL;
}

TOperandInteger* Transaction::LookupInteger(size_t var, bool required)
{
  TOperand *res = Lookup(var, required);
  return res ? res->AsInteger() : NULL;
}

/////////////////////////////////////////////////////////////////////
// Transaction submission
/////////////////////////////////////////////////////////////////////

ConfigOption timeout(CK_UInt, "timeout", "0",
                     "hard analysis timeout, 0 for no timeout");

ConfigOption trans_remote(CK_String, "remote", "",
                          "remote manager address:port");

ConfigOption trans_initial(CK_Flag, "initial", NULL,
                           "whether to submit an initialize transaction");

// flag for one-time setup.
static bool prepared_analysis = false;

// whether we are submitting transactions to a remote manager.
static bool remote_submit = false;

// descriptor for remote submission.
static int remotefd = 0;

// buffer to hold packet contents for remote submission.
static Buffer remote_buf("Buffer_remote_transaction");

// these handlers abort because trying to do normal program teardown
// can deadlock when freeing memory. we really should be using a
// thread unsafe libc.

static void termination_handler(int signal)
{
  logout << "ERROR: Termination signal received, aborting..." << endl << flush;
  abort();
}

static void timeout_handler(int signal)
{
  logout << "ERROR: Analysis timed out, aborting..." << endl << flush;
  abort();
}

void AnalysisPrepare(const char *remote_address)
{
  Assert(!prepared_analysis);
  prepared_analysis = true;

  signal(SIGPIPE, SIG_IGN);
  signal(SIGINT,  termination_handler);
  signal(SIGTERM, termination_handler);
  signal(SIGALRM, timeout_handler);

  // we can get the remote address either from our argument or the option.
  if (trans_remote.IsSpecified()) {
    Assert(!remote_address);
    remote_address = trans_remote.StringValue();
  }

  // no additional preparation needed for local processing
  if (!remote_address)
    return;

  const char *colon_pos = strchr(remote_address, ':');
  if (colon_pos == NULL) {
    logout << "ERROR: malformed remote address: missing ':'" << endl << flush;
    abort();
  }

  char address[512];
  if (colon_pos - remote_address + 1 > (long) sizeof(address)) {
    logout << "ERROR: malformed remote address: too long" << endl << flush;
    abort();
  }

  memcpy(address, remote_address, colon_pos - remote_address);
  address[colon_pos - remote_address] = '\0';

  long port;
  if (!StringToInt(colon_pos + 1, &port)) {
    logout << "ERROR: malformed remote address: invalid port" << endl << flush;
    abort();
  }

  int ret;

  remotefd = socket(PF_INET, SOCK_STREAM, 0);
  if (remotefd == -1) {
    logout << "ERROR: socket() failure: " << strerror(errno) << endl << flush;
    abort();
  }

  struct sockaddr_in addr;
  memset(&addr, 0, sizeof(addr));

  ret = inet_pton(PF_INET, address, &addr.sin_addr);
  if (ret == 0) {
    logout << "ERROR: invalid address for inet_pton()" << endl << flush;
    abort();
  }
  if (ret == -1) {
    logout << "ERROR: inet_pton() failure: " << strerror(errno) << endl << flush;
    abort();
  }

  addr.sin_family = PF_INET;
  addr.sin_port = htons((unsigned short) port);

  ret = connect(remotefd, (sockaddr*) &addr, sizeof(addr));
  if (ret == -1) {
    // we get ECONNREFUSED when the manager is not there anymore.
    // treat this as a success, presumably the manager finished its work
    // and shut down.
    if (errno == ECONNREFUSED) {
      logout << "Manager has been terminated, exiting..." << endl << flush;
      exit(0);
    }

    logout << "ERROR: connect() failure: " << strerror(errno) << endl << flush;
    abort();
  }

  remote_submit = true;
}

bool IsAnalysisRemote()
{
  Assert(prepared_analysis);
  return remote_submit;
}

uint32_t GetTimeout()
{
  return timeout.UIntValue();
}

void ResetTimeout(uint32_t offset)
{
  uint32_t seconds = timeout.UIntValue();
  if (seconds != 0)
    alarm(seconds + offset);
}

void AnalysisCleanup()
{
  TransactionBackend::FinishBackend();
  prepared_analysis = false;
}

void AnalysisFinish(int code)
{
  AnalysisCleanup();
  exit(code);
}

void SubmitTransaction(Transaction *t)
{
  static BaseTimer transaction_timer("submit_transaction");
  Timer _timer(&transaction_timer);

  Assert(prepared_analysis);

  if (remote_submit) {
    Assert(remote_buf.pos == remote_buf.base);
    remote_buf.Ensure(UINT32_LENGTH);
    remote_buf.pos += UINT32_LENGTH;
    t->Write(&remote_buf);

    Buffer write_buf(remote_buf.base, remote_buf.pos - remote_buf.base);

    bool success = WritePacket(remotefd, &write_buf);
    if (!success) {
      logout << "ERROR: Could not write entire transaction." << endl;
      Assert(false);
    }

    remote_buf.Reset();

    // keep reading and blocking until we get a response.
    do {
      success = ReadPacket(remotefd, &remote_buf);
    } while (!success);

    size_t data_length = remote_buf.pos - remote_buf.base - UINT32_LENGTH;

    // make a new buffer to hold the contents read from the buffer,
    // as ReadResult may put internal pointers to the buffer into
    // the transaction. if we use a single buffer the data for this
    // transaction's result will be invalidated when the next transaction
    // is submitted.

    Buffer *read_buf = new Buffer(data_length);
    t->AddBuffer(read_buf);

    memcpy(read_buf->base, remote_buf.base + UINT32_LENGTH, data_length);
    remote_buf.Reset();

    if (!t->ReadResult(read_buf)) {
      logout << "ERROR: Corrupt packet data." << endl;
      Assert(false);
    }
  }
  else {
    t->Execute();
  }

  Assert(t->HasSuccess());
}

void SubmitInitialTransaction()
{
  if (remote_submit) {
    Transaction *t = new Transaction();
    t->SetInitial();
    SubmitTransaction(t);
    delete t;
  }
}

void SubmitFinalTransaction()
{
  if (remote_submit) {
    Transaction *t = new Transaction();
    t->SetFinal();
    SubmitTransaction(t);
    delete t;
  }
}

NAMESPACE_XGILL_END
