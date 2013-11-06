all:
	for i in `ls *.cfg`; do \
		echo "Translating $$i into Hampi format";\
		../../cfg2hmp.sh -s 20 -e $$i >> ../hampi-tests/$$i.hmp;\
	done
