SUBDIRS =  cfganalyzer-tests hampi-tests

.PHONY: $(SUBDIRS)

all: hampi-tests
	@echo "Performance Testing Completed"

cfganalyzer-tests:
	$(MAKE) -C $@

create-perftest-gold:
	$(MAKE) -C hampi-tests create-perftest-gold

hampi-tests:
	$(MAKE) -C $@