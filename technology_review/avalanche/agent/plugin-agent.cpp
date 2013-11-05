/*---------------------------------------------------------------------------*/
/*------------------------------- AVALANCHE ---------------------------------*/
/*------------------- Remote valgrind agent for Avalanche. ------------------*/
/*---------------------------- plugin-agent.cpp -----------------------------*/
/*---------------------------------------------------------------------------*/

/*
   Copyright (C) 2011 Michael Ermakov
      mermakov@ispras.ru

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/
 
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <iostream>
#include <sstream>
#include <unistd.h>
#include <fcntl.h>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <unistd.h>
#include <cerrno>

#include "util.h"

using namespace std;

enum Kind
{
    TG,
    OTHER
};

#define DEBUG

int avalanche_fd;
pid_t pid = 0;
Kind kind;
bool no_coverage;
bool check_prediction;
bool dump_prediction;
bool check_danger;
bool dump_calls;
bool network;
bool check_argv;
string temp_dir;
bool killed = false;

static bool parseArg(char **p_arg)
{
    char *arg = *p_arg;
    if (!strcmp(arg, "--no-coverage=yes"))
    {
        no_coverage = true;
    }
    else if (!strcmp(arg, "--check-prediction=yes"))
    {
        check_prediction = true;
    }
    else if (!strcmp(arg, "--dump-prediction=yes"))
    {
        dump_prediction = true;
    }
    else if (!strcmp(arg, "--check-danger=yes"))
    {
        check_danger = true;
    }
    else if (!strcmp(arg, "--dump-file=calldump.log"))
    {
        dump_calls = true;
    }
    else if (!strcmp(arg, "--sockets=yes") || !strcmp(arg, "--datagrams=yes"))
    {
        network = true;
    }
    else if (strstr(arg, "--check-argv="))
    {
        check_argv = true;
    }
    else if (strstr(arg, "--tool=tracegrind"))
    {
        kind = TG;
    }
    else if (strstr(arg, "--tool="))
    {
        kind = OTHER;
    }
    else if (strstr(arg, "--alarm="))
    {
        int alarm_value = strtol(arg + strlen("--alarm="), NULL, 10);
        alarm(alarm_value);
    }
    else if (strstr(arg, "argv.log"))
    {
        free(arg);
        string new_arg = string("--file=") + temp_dir + string("argv.log");
        int len = new_arg.length();
        *p_arg = (char*) malloc(len + 1);
        strncpy(*p_arg, new_arg.c_str(), len);
        (*p_arg)[len] = '\0';
    }
    return true;
}

void sigalarm_handler(int signo)
{
    if (kind == OTHER)
    {
        kill(pid, SIGINT);
        killed = true;
    }
}    

static void readToFile(string file_name)
{
    int length, i = 0;
    char c;
    readFromSocket(avalanche_fd, &length, sizeof(int));
    int file_d = 
           open(file_name.c_str(), O_CREAT | O_TRUNC | O_WRONLY, 
                S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
    if (file_d < 0)
    {
        throw file_name.c_str();
    }
    while (i < length)
    {
        readFromSocket(avalanche_fd, &c, 1);
        if (write(file_d, &c, 1) < 1)
        {
            close(file_d);
            throw "error writing to file";
        }
        i ++;
    }
    close(file_d);
}
            

static int readAndExec(const string &prog_dir, int argc, char** argv)
{
    int length, args_num;
    char **args;
    char util_c;
    no_coverage = false;
    
    int extra_args = 5;

    readFromSocket(avalanche_fd, &args_num, sizeof(int));
    args = (char **) calloc (args_num + extra_args + 1, sizeof(char *));
    string valgrind_path = prog_dir + "../lib/avalanche/valgrind";
    args[0] = strdup(valgrind_path.c_str());
    
    /* Read --tool= option */
    readFromSocket(avalanche_fd, &length, sizeof(int));
    args[1] = (char *) malloc(length + 1);
    readFromSocket(avalanche_fd, args[1], length);
    args[1][length] = '\0';
    parseArg(&(args[1]));
    readFromSocket(avalanche_fd, &util_c, 1);

    ostringstream ss;
    ss << "--remote-fd=" << avalanche_fd;

    switch(kind)
    {
        case TG:    args[4] = strdup(ss.str().c_str());
                    break;
        case OTHER: extra_args --;
                    break;
    }
    args[2] = strdup((string("--temp-dir=") + temp_dir).c_str());
    args[3] = strdup((string("--log-file=") + temp_dir + 
                      string("execution.log")).c_str());
    for (int i = extra_args; i < args_num + extra_args - 1; i ++)
    {
        readFromSocket(avalanche_fd, &length, sizeof(int));
        args[i] = (char *) malloc(length + 1);
        readFromSocket(avalanche_fd, args[i], length);
        args[i][length] = '\0';
        parseArg(&(args[i]));
        readFromSocket(avalanche_fd, &util_c, 1);
        if (util_c)
        {
            char * file_name = strchr(args[i], '=');
            if (file_name == NULL)
            {
                file_name = args[i];
            }
            else
            {
                file_name ++;
            }
            readToFile(file_name);
        }
    }
    if (check_prediction)
    {
        readToFile(temp_dir + string("prediction.log"));
    }
    if (network)
    {
        readToFile(temp_dir + string("replace_data"));
    }
    if (check_argv)
    {
        readToFile(temp_dir + string("arg_lengths"));
    }
    args[args_num + extra_args] = NULL;
    pid = fork();
    if (pid == 0)
    {
#ifdef DEBUG
        cout << endl << "executing command: " << endl;
        for (int i = 0; i < args_num + extra_args; i ++)
        {
            cout << args[i] << " ";
        }
        cout << endl;
#endif
        int tmpout_fd = 
               open("tmp_stdout", O_CREAT | O_TRUNC | O_WRONLY,
                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
        int tmperr_fd = 
               open("tmp_stderr", O_CREAT | O_TRUNC | O_WRONLY,
                    S_IRUSR | S_IROTH | S_IRGRP | S_IWUSR | S_IWOTH | S_IWGRP);
        dup2(tmpout_fd, STDOUT_FILENO);
        dup2(tmperr_fd, STDERR_FILENO);
        execvp(args[0], args);
    }
    int status;
    pid_t ret_proc = ::waitpid(pid, &status, 0);
#ifdef DEBUG
    cout << "plugin finished work";
#endif
    if (ret_proc == (pid_t)(-1)) 
    {
        return 1;
    }
    for (int i = 0; i < args_num + extra_args; i ++)
    {
        free(args[i]);
    }
    free(args);
#ifdef DEBUG
    if (!WIFEXITED(status))
    {
        cout << " (crashed)" << endl;
    }
    else 
    {
        cout << endl;
    }
#endif
    if ((WEXITSTATUS(status) == 126) ||
        (WEXITSTATUS(status) == 127)) //Problem with executable
    {
        int fd = open("tmp_stderr", O_RDONLY, S_IRUSR);
        lseek(fd, SEEK_SET, 0);
        struct stat f_stat;
        fstat(fd, &f_stat);
        char buf[f_stat.st_size + 1];
        read(fd, buf, f_stat.st_size);
        buf[f_stat.st_size] = '\0';
        cout << buf << endl;
        return 1;
    }
    if (killed == true)
    {
        killed = false;
        return -1;
    }
    return ((WIFEXITED(status)) ? 0 : -1);
}

static void writeFromFile(string file_name)
{
    int file_d = open(file_name.c_str(), O_RDONLY, S_IRUSR);
    if (file_d < 0)
    {
        throw file_name.c_str();
    }
    struct stat file_info;
    if (fstat(file_d, &file_info) < 0)
    {
        close(file_d);
        throw "fstat failed";
    }
    int size = file_info.st_size;
    char c;
    int i = 0;
    writeToSocket(avalanche_fd, &size, sizeof(int));
    while(i < size)
    {
        if (read(file_d, &c, 1) < 1)
        {
            close(file_d);
            throw "error reading from file";
        }
        writeToSocket(avalanche_fd, &c, 1);
        i ++;
    }
    close(file_d);
}

static int passResult(int ret_code)
{
    writeToSocket(avalanche_fd, &ret_code, sizeof(int));
    if (ret_code == 1)
    {
        return -1;
    }
    switch(kind)
    {
        case TG: 
            writeFromFile(temp_dir + string("offsets.log"));
            if (dump_prediction)
            {
                writeFromFile(temp_dir + string("actual.log"));
            }
            if (dump_calls)
            {
                writeFromFile("calldump.log");
            }
            if (network)
            {
                writeFromFile(temp_dir + string("replace_data"));
            }
            if (check_argv)
            {
                writeFromFile(temp_dir + string("argv.log"));
            }
            break;
        case OTHER:
            if (!no_coverage)
            {
                writeFromFile(temp_dir + string("basic_blocks.log"));
            }
            writeFromFile(temp_dir + string("execution.log"));
            break;
        default: break;
    }
    return 0;
}

static string findInPath(const string &name)
{
    const char *var = getenv("PATH");
    if (var == NULL || var[0] == '\0') return string();

    string dirs = var;
    for (size_t begin_pos = 0; begin_pos < dirs.size(); ) {
        size_t colon_pos = dirs.find(':', begin_pos);
        size_t end_pos = (colon_pos == string::npos) ? dirs.size() : colon_pos;
        string dir = dirs.substr(begin_pos, end_pos - begin_pos);
        string file_name = dir + "/" + name;
        if (access(file_name.c_str(), X_OK) == 0) {
            return file_name;
        }
        begin_pos = end_pos + 1;
    }

    return string();
}

int main(int argc, char** argv)
{
    bool opt_error = false;
    int port = 0;
    string host = string("");
    temp_dir = string("./");
    for (int i = 1; i < argc; i ++)
    {
        if (strstr(argv[i], "--port=") == argv[i])
        {
            port = atoi(argv[i] + strlen("--port="));
            if ((port <= 0) || (port >= 0xFFFF))
            {
                opt_error = true;
                break;
            }
        }
        else if (strstr(argv[i], "--host=") == argv[i])
        {
            host = string(argv[i] + strlen("--host="));
        }
        else if (strstr(argv[i], "--temp-dir=") == argv[i])
        {
            temp_dir = string(argv[i] + strlen("--temp-dir="));
        }
    }
    if (opt_error || (port == 0))
    {
        cout << "Usage: plugin-agent --port=<port> [--host=<host>] [--temp-dir=<dir>]\n";
        exit(EXIT_FAILURE);
    }
    if (temp_dir != "./")
    {
        if (*(temp_dir.end() - 1) != '/')
        {
            temp_dir += string("/");
        }
#define TMP_DIR_TEMPLATE_SIZE 6
        temp_dir += string("avalanche-");
        srand(time(NULL));
        for (int i = 0; i < TMP_DIR_TEMPLATE_SIZE; i ++)
        {
            ostringstream ss;
            ss << (char)('a' + rand() % ('z' - 'a'));
            temp_dir += ss.str();
        }
        temp_dir += '/';
#undef TMP_DIR_TEMPLATE_SIZE
    }
    if (mkdir(temp_dir.c_str(), S_IRWXU) == -1)
    {
        if (errno != EEXIST)
        {
            perror("mkdir failed");
            temp_dir = string("");
        }
    }
    string prog_name = argv[0];
    size_t slash_pos = prog_name.find_last_of('/');
    if (slash_pos == string::npos) {
        prog_name = findInPath(prog_name);
        slash_pos = prog_name.find_last_of('/');
    }
    string prog_dir = prog_name.substr(0, slash_pos + 1);

    int socket_fd;
    struct sockaddr_in st_socket_addr;
    socket_fd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    if(socket_fd == -1)
    {
        perror("can not create socket");
        exit(EXIT_FAILURE);
    }
    if (host != "")
    {
        memset(&st_socket_addr, 0, sizeof(struct sockaddr_in));

        st_socket_addr.sin_family = AF_INET;
        st_socket_addr.sin_port = htons(port);
        int res = inet_pton(AF_INET, host.c_str(), &st_socket_addr.sin_addr);
        if (res <= 0)
        {
            perror("invalid host address");
            exit(EXIT_FAILURE);
        }

        if (connect(socket_fd, (const struct sockaddr*)&st_socket_addr, sizeof(struct sockaddr_in)) < 0)
        {
            perror("connect failed");
            close(socket_fd);
            exit(EXIT_FAILURE);
        }
        avalanche_fd = socket_fd;
    }
    else
    {
        int on = 1;
        setsockopt(socket_fd, SOL_SOCKET, SO_REUSEADDR, &on, sizeof(on));

        memset(&st_socket_addr, 0, sizeof(struct sockaddr_in));
        st_socket_addr.sin_family = AF_INET;  
        st_socket_addr.sin_port = htons(port);
        st_socket_addr.sin_addr.s_addr = INADDR_ANY;

        if(bind(socket_fd, (const struct sockaddr*)&st_socket_addr, sizeof(struct sockaddr_in)) < 0)
        {
            perror("bind failed");
            close(socket_fd);
            exit(EXIT_FAILURE);
        }

        if(listen(socket_fd, 10) < 0)
        {
            perror("listen failed");
            close(socket_fd);
            exit(EXIT_FAILURE);
        }

        avalanche_fd = accept(socket_fd, NULL, NULL);
        if (avalanche_fd < 0)
        {
            perror("accept failed");
            close(socket_fd);
            exit(EXIT_FAILURE);
        }
        close(socket_fd);
    }

    signal(SIGALRM, sigalarm_handler);

    try {
        writeToSocket(avalanche_fd, "avalanche", strlen("avalanche"));
        int size = sizeof(long);
        writeToSocket(avalanche_fd, &size, sizeof(int));
        while(1)
        {
            no_coverage = false;
            dump_prediction = false;
            check_prediction = false;
            check_danger = false;
            dump_calls = false;
            network = false;
            check_argv = false;
            int res = readAndExec(prog_dir, argc, argv);
            if (res == -2)
            {
                cout << "end of communication: no more requests" << endl;
                break;
            }
            if (passResult(res) < 0)
            {
                break;
            }
        }
    }
    catch(const char * error_msg)
    {
        cout << "end of communication: " << error_msg << endl;
    }
    shutdown(avalanche_fd, SHUT_RDWR);
    unlink("tmp_stdout");
    unlink("tmp_stderr");
    unlink((temp_dir + string("trace.log")).c_str());
    unlink((temp_dir + string("dangertrace.log")).c_str());
    unlink((temp_dir + string("actual.log")).c_str());
    unlink((temp_dir + string("arg_lengths")).c_str());
    unlink((temp_dir + string("replace_data")).c_str());
    unlink((temp_dir + string("prediction.log")).c_str());
    unlink((temp_dir + string("basic_blocks.log")).c_str());
    unlink((temp_dir + string("execution.log")).c_str());
    unlink((temp_dir + string("argv.log")).c_str());
    unlink((temp_dir + string("divergence.log")).c_str());
    unlink((temp_dir + string("offsets.log")).c_str());

    /* STP multi-threading currently cannot be used in split mode */
    
    /* We don't pass thread number with options so we don't know which
             files were created and have to use exec */
             
    //system((string("rm ") + temp_dir + string("replace_data*")).c_str());
    
    /* We have argv.log_i with multiple threads for STP since argv.log
             is treated like an input file specified by '--filename=' */
             
    //system((string("rm ") + temp_dir + string("argv.log*")).c_str());
    //system((string("rm ") + temp_dir + string("basic_blocks*.log")).c_str());
    if ((temp_dir != "") && (temp_dir != "./"))
    {
        if (rmdir(temp_dir.c_str()) < 0)
        {
            if (errno != ENOENT)
            {
                perror((string("cannot delete ") + temp_dir).c_str());
            }
        }
    }
    return 0;
}
        
