IMPACTEDML = extraction/impacted/ocaml/impacted.ml extraction/impacted/ocaml/impacted.mli
IMPACTEDRBTML = extraction/impacted-rbt/ocaml/impacted_rbt.ml extraction/impacted-rbt/ocaml/impacted_rbt.mli

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
	coq_makefile -f _CoqProject -o Makefile.coq \
	  -extra '$(IMPACTEDML)' \
	    'extraction/impacted/coq/extract_impacted.v core/finn.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/impacted/coq/extract_impacted.v' \
	  -extra '$(IMPACTEDRBTML)' \
	    'extraction/impacted-rbt/coq/extract_impacted_rbt.v core/finn_set.vo' \
	    '$$(COQC) $$(COQDEBUG) $$(COQFLAGS) extraction/impacted-rbt/coq/extract_impacted_rbt.v'

$(IMPACTEDML) $(IMPACTEDRBTML): Makefile.coq
	$(MAKE) -f Makefile.coq $@

.PHONY: all default quick clean impacted $(IMPACTEDML) $(IMPACTEDRBTML)

.NOTPARALLEL: $(IMPACTEDML)
.NOTPARALLEL: $(IMPACTEDRBTML)
