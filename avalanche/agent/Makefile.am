bin_PROGRAMS = av-agent av-dist plugin-agent

av_agent_CFLAGS = -Wno-deprecated
av_dist_CFLAGS = -Wno-deprecated

CXXLD = $(CC)
LIBS = -static-libgcc -Wl,-Bstatic,-lstdc++,-Bdynamic

av_agent_SOURCES = \
       agent.cpp \
       util.cpp 

av_dist_SOURCES = \
       dist.cpp \
       util.cpp

plugin_agent_SOURCES = \
       plugin-agent.cpp \
       util.cpp

noinst_HEADERS = util.h

