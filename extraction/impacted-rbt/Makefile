OCAMLBUILD = ocamlbuild -tag safe_string -I ocaml -cflag -g -package extlib
OCAMLBUILD_JSON = $(OCAMLBUILD) -package yojson

IMPACTEDRBT = ocaml/impacted_rbt.ml ocaml/impacted_rbt.mli
CHANGE = ocaml/util.ml ocaml/change_impact.ml ocaml/change_impact.mli

default: filtering.native

filtering.native: $(IMPACTEDRBT) $(CHANGE) ocaml/filtering.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) filtering.native

topfiltering.native: $(IMPACTEDRBT) $(CHANGE) ocaml/topfiltering.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) topfiltering.native

filteringinv.native: $(IMPACTEDRBT) $(CHANGE) ocaml/filteringinv.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) filteringinv.native

$(IMPACTEDRBT):
	+$(MAKE) -C ../.. extraction/impacted-rbt/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(IMPACTEDRBT)

.NOTPARALLEL: $(IMPACTEDRBT)
