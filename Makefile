include Makefile.ml-files

all: default

default: Makefile.coq
	$(MAKE) -f Makefile.coq

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall
	rm -f Makefile.coq Makefile.coq.conf
	$(MAKE) -C extraction/impacted clean
	$(MAKE) -C extraction/impacted-rbt clean

impacted:
	+$(MAKE) -C extraction/impacted filtering.native filteringinv.native topfiltering.native

impacted-rbt:
	+$(MAKE) -C extraction/impacted-rbt filtering.native filteringinv.native topfiltering.native

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

$(IMPACTEDML) $(IMPACTEDRBTML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all default quick clean impacted $(IMPACTEDML) $(IMPACTEDRBTML)

.NOTPARALLEL: $(IMPACTEDML)
.NOTPARALLEL: $(IMPACTEDRBTML)
