noinst_PROGRAMS = entry divclient multiple_client multiple_client2 writeserver sample2 uninit mleak separate_analysis_sample dist dist3 data_race

CFLAGS += -O0 -g

if !BIONIC
  data_race_CFLAGS = -pthread
endif

entry_SOURCES = entry.c
dist_SOURCES = dist.c
dist3_SOURCES = dist3.c
divclient_SOURCES = divclient.c
multiple_client_SOURCES = multiple_client.c
multiple_client2_SOURCES = multiple_client2.c
writeserver_SOURCES = writeserver.c
sample2_SOURCES = sample2.c
uninit_SOURCES = uninit.c
mleak_SOURCES = mleak.c
separate_analysis_sample_SOURCES = separate_analysis_sample.c
data_race_SOURCES = data_race.c


dist_noinst_DATA = seed
