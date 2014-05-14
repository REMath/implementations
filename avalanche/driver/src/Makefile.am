bin_PROGRAMS = avalanche

INCLUDES = -I../include

avalanche_CFLAGS = -Wno-deprecated

if !BIONIC
  LDFLAGS += -pthread
endif

CXXLD = $(CC)
LIBS = -static-libgcc -Wl,-Bstatic,-lstdc++,-Bdynamic

avalanche_SOURCES = \
       Error.cpp \
       Entry.cpp \
       LocalExecutor.cpp \
       RemotePluginExecutor.cpp \
       ExecutionManager.cpp \
       Logger.cpp \
       OptionParser.cpp \
       PluginExecutor.cpp \
       FileBuffer.cpp \
       SocketBuffer.cpp \
       ExecutionLogBuffer.cpp \
       Input.cpp \
       STP_Executor.cpp \
       TmpFile.cpp \
       Thread.cpp \
       Monitor.cpp
