CC = g++ -Wall
CFLAGS = -O3 

#CFLAGS = -O3 -DNDEBUG
#MFLAGS = 
#LINKFLAGS = --static

ifeq (solaris, $(OSTYPE))
  MFLAGS = -D_NEED_REDEFINE_RAND_MAX_
endif

RANLIB = ranlib
AR = ar

.SUFFIXES: .o .cpp 

HEADERS = zchaff_base.h zchaff_clsgen.h zchaff_header.h zchaff_version.h zchaff_dbase.h zchaff_solver.h

SOLVER_SRCS = sat_solver.cpp 
SOLVER_OBJS = $(SOLVER_SRCS:.cpp=.o)

LIB_SRCS =  zchaff_utils.cpp \
	    zchaff_solver.cpp\
	    zchaff_base.cpp \
	    zchaff_dbase.cpp \
	    zchaff_c_wrapper.cpp \
	    zchaff_cpp_wrapper.cpp \

LIB_OBJS = $(LIB_SRCS:.cpp=.o)


zchaff:   $(SOLVER_OBJS) libsat.a SAT.h
	  $(CC) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) $(SOLVER_OBJS) libsat.a -o zchaff 

zverify_df: zverify_df.cpp
	  $(CC) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zverify_df.cpp -o zverify_df

zminimal: zminimal.cpp libsat.a
	  $(CC) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) zminimal.cpp libsat.a -o zminimal

cnf_stats: cnf_stats.cpp
	  $(CC) $(LINKFLAGS) $(CFLAGS) $(MFLAGS) cnf_stats.cpp -o cnf_stats

$(LIB_OBJS): $(HEADERS) Makefile

$(SOLVER_OBJS): $(SOLVER_SRCS) SAT.h Makefile

zchaff_c_wrapper.cpp:	zchaff_wrapper.wrp
		sed 's/EXTERN/extern \"C\"/' zchaff_wrapper.wrp > zchaff_c_wrapper.cpp

zchaff_cpp_wrapper.cpp:	zchaff_wrapper.wrp
		sed 's/EXTERN//' zchaff_wrapper.wrp > zchaff_cpp_wrapper.cpp
SAT_C.h:
	sed 's/gid = 0/gid/' SAT.h > SAT_C.h

libsat.a:   $(LIB_OBJS)
	@rm -f libsat.a
	$(AR) cr libsat.a $(LIB_OBJS)
	$(RANLIB) libsat.a

.cpp.o:
	$(CC) $(CFLAGS) $(MFLAGS) -c $< 

clean:	
	rm -f *.o libsat.a zchaff *wrapper.cpp zminimal zverify_df cnf_stats SAT_C.h

all: zchaff zverify_df zminimal cnf_stats
