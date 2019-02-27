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

hierarchical.native: $(IMPACTEDRBT) $(CHANGE) ocaml/hierarchical.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) hierarchical.native

hierarchicalignore.native: $(IMPACTEDRBT) $(CHANGE) ocaml/hierarchicalignore.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) hierarchicalignore.native

hierarchicalimpacted.native: $(IMPACTEDRBT) $(CHANGE) ocaml/hierarchicalimpacted.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) hierarchicalimpacted.native

hierarchicalignoreimpacted.native: $(IMPACTEDRBT) $(CHANGE) ocaml/hierarchicalignoreimpacted.ml
	perl scripts/remove_module.pl ocaml/impacted_rbt
	$(OCAMLBUILD_JSON) hierarchicalignoreimpacted.native

$(IMPACTEDRBT):
	+$(MAKE) -C ../.. extraction/impacted-rbt/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(IMPACTEDRBT)

.NOTPARALLEL: $(IMPACTEDRBT)
