OCAMLBUILD = ocamlbuild -tag safe_string -I ocaml -cflag -g -package extlib
OCAMLBUILD_JSON = $(OCAMLBUILD) -package yojson

IMPACTED = ocaml/impacted.ml ocaml/impacted.mli
CHANGE = ocaml/util.ml ocaml/change_impact.ml ocaml/change_impact.mli

default: filtering.native

filtering.native: $(IMPACTED) $(CHANGE) ocaml/filtering.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) filtering.native

topfiltering.native: $(IMPACTED) $(CHANGE) ocaml/topfiltering.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) topfiltering.native

filteringinv.native: $(IMPACTED) $(CHANGE) ocaml/filteringinv.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) filteringinv.native

hierarchical.native: $(IMPACTED) $(CHANGE) ocaml/hierarchical.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchical.native

modified.native: $(IMPACTED) $(CHANGE) ocaml/modified.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) modified.native

hierarchicalignore.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalignore.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalignore.native

hierarchicalimpacted.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalimpacted.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalimpacted.native

hierarchicalignoreimpacted.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalignoreimpacted.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalignoreimpacted.native

hierarchicalpt.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalpt.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalpt.native

hierarchicalignorept.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalignorept.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalignorept.native

hierarchicalignoreimpactedpt.native: $(IMPACTED) $(CHANGE) ocaml/hierarchicalignoreimpactedpt.ml
	perl scripts/remove_module.pl ocaml/impacted
	$(OCAMLBUILD_JSON) hierarchicalignoreimpactedpt.native

ids.native: ocaml/ids.ml
	$(OCAMLBUILD_JSON) ids.native

neighbors.native: ocaml/neighbors.ml
	$(OCAMLBUILD_JSON) neighbors.native

$(IMPACTED):
	+$(MAKE) -C ../.. extraction/impacted/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(IMPACTED)

.NOTPARALLEL: $(IMPACTED)
