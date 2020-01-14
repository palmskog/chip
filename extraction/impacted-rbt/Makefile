OCAMLBUILD = ocamlbuild -tag safe_string -I ocaml -cflag -g -package extlib
OCAMLBUILD_JSON = $(OCAMLBUILD) -package yojson
SED = sed -i \
 -e s/val\ predT\ \:\ \'a1\ simpl\_pred//g \
 -e s/val\ pred_of_argType\ \:\ \'a1\ simpl\_pred//g \
 -e s/val\ simplPredType\ \:\ \'a1\ predType//g

IMPACTEDRBTML = ocaml/impacted_rbt.ml
IMPACTEDRBTMLI = ocaml/impacted_rbt.mli
CHANGE = ocaml/util.ml ocaml/change_impact.ml ocaml/change_impact.mli

default: filtering.native

filtering.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/filtering.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) filtering.native

topfiltering.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/topfiltering.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) topfiltering.native

filteringinv.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/filteringinv.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) filteringinv.native

hierarchical.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchical.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchical.native

hierarchicalignore.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchicalignore.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchicalignore.native

hierarchicalimpacted.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchicalimpacted.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchicalimpacted.native

hierarchicalignoreimpacted.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchicalignoreimpacted.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchicalignoreimpacted.native

hierarchicalignorept.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchicalignorept.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchicalignorept.native

hierarchicalignoreimpactedpt.native: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI) $(CHANGE) ocaml/hierarchicalignoreimpactedpt.ml
	$(SED) $(IMPACTEDRBTMLI)
	$(OCAMLBUILD_JSON) hierarchicalignoreimpactedpt.native

$(IMPACTEDRBTML) $(IMPACTEDRBTMLI):
	+$(MAKE) -C ../.. extraction/impacted-rbt/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(IMPACTEDRBTML) $(IMPACTEDRBTMLI)

.NOTPARALLEL: $(IMPACTEDRBTML) $(IMPACTEDRBTMLI)
