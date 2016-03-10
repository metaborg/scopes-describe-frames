.PHONY: coq clean

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

html: Makefile.coq
	$(MAKE) -f Makefile.coq html

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: Makefile.source
	coq_makefile -f Makefile.source -o Makefile.coq


