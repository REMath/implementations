REGRESS_LOG=`date +%Y-%m-%d`"-hampi-slowtests-regress.log"
all:
	@for i in `ls *.hmp`; do \
		echo "Running Hampi on slow example $$i" >> $(REGRESS_LOG); \
		echo "time -f %U ../../hampi.sh $$i " >> $(REGRESS_LOG);\
		(time -f %U ../../hampi.sh $$i >> $(REGRESS_LOG))  2>> $$i.reg; \
		echo " " >> $(REGRESS_LOG); \
		echo "=============================================" >> $(REGRESS_LOG); \
		echo " " >> $(REGRESS_LOG); \
	done

	for i in `ls *.hmp`; do cat $$i.gold; cat $$i.reg; echo "----------"; done

create-perftest-gold:

	@for i in `ls *.hmp`; do \
		time -f %U ../../hampi.sh $$i 2>> $$i.gold; \
	done

clean:
	rm -rf *~ *.reg