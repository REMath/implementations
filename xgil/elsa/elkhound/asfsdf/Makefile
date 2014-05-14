# Makefile for parsgen/asfsdf

ssx.perf.txt:
	for n in 5 7 9 11 13 15 17 19 21; do \
	  echo -n "$$n: "; \
	  sglr -p SSx.trm.tbl -i ../ssx.in/$$n.in >/dev/null; \
	done &>$@

ssx.notree.perf.txt:
	for n in 5 15 25 35 45 55 65 75 85 99; do \
	  echo -n "$$n: "; \
	  sglr -n -p SSx.trm.tbl -i ../ssx.in/$$n.in; \
	done &>$@

eeb.perf.txt:
	for n in 5 6 7 8 9 10; do \
	  echo -n "$$n: "; \
	  sglr -p EEb.trm.tbl -i ../eeb.in/$$n.in >/dev/null; \
	done &>$@

eeb.notree.perf.txt:
	for n in 10 20 50 100 200 300 400 500; do \
	  echo -n "$$n: "; \
	  sglr -n -p EEb.trm.tbl -i ../eeb.in/$$n.in; \
	done &>$@

sssx.perf.txt:
	for n in 5 7 10 12 14; do \
	  echo -n "$$n: "; \
	  sglr -p SSSx.trm.tbl -i ../sssx.in/$$n.in >/dev/null; \
	done &>$@

sssx.notree.perf.txt:
	for n in 5 10 15 20 25 30 35 40 45 50; do \
	  echo -n "$$n: "; \
	  sglr -n -p SSSx.trm.tbl -i ../sssx.in/$$n.in; \
	done &>$@

efa.perf.txt:
	for fn in ../efa.in/*; do \
	  for count in 1 2 3 4 5; do \
	    echo -n "$$fn: "; \
	    sglr -p EFa.trm.tbl -i $$fn >/dev/null || echo "failed"; \
	  done; \
	done &>$@

efa.notree.perf.txt:
	for fn in ../efa.in/*; do \
	  for count in 1 2 3 4 5; do \
	    echo -n "$$fn: "; \
	    sglr -n -p EFa.trm.tbl -i $$fn; \
	  done; \
	done &>$@

%.csv: %.txt
	cat $^ | grep cycles | \
	perl -p -e 's/^[^:]*\D(\d+)\D.*: cycles: (\d+)$$/$$1, $$2/' >$@
