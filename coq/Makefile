.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq

clean:
	rm -f Makefile.coq 
	rm -f */*.vo */*.v.d */*.glob */.*.aux */*~ */.#* 
	rm -f */*/*.vo */*/*.v.d */*/*.glob */*/.*.aux */*/*~ */*/.#*

