SUBDIRS = stp-jni cfganalyzer-2007-12-03

.PHONY: $(SUBDIRS)

all: $(SUBDIRS)

stp-jni cfg-analyzer-2007-12-03:
	$(MAKE) -C $@

teststp:
	$(MAKE) -C stp-jni teststp

clean:
	rm -rf *~ libsat.a libstp.a libSTPJNI.so STPJNI.jar
	$(MAKE) -C stp-jni clean