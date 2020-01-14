OCAMLBUILD = ocamlbuild -tag safe_string -I ocaml -cflag -g -package extlib
OCAMLBUILD_JSON = $(OCAMLBUILD) -package yojson
SED = sed -i \
 -e s/val\ predT\ \:\ \'a1\ simpl\_pred//g \
 -e s/val\ pred_of_argType\ \:\ \'a1\ simpl\_pred//g \
 -e s/val\ simplPredType\ \:\ \'a1\ predType//g

IMPACTEDML = ocaml/impacted.ml
IMPACTEDMLI = ocaml/impacted.mli
CHANGE = ocaml/util.ml ocaml/change_impact.ml ocaml/change_impact.mli

default: filtering.native

filtering.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/filtering.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) filtering.native

topfiltering.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/topfiltering.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) topfiltering.native

filteringinv.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/filteringinv.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) filteringinv.native

hierarchical.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchical.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchical.native

modified.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/modified.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) modified.native

hierarchicalignore.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalignore.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalignore.native

hierarchicalimpacted.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalimpacted.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalimpacted.native

hierarchicalignoreimpacted.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalignoreimpacted.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalignoreimpacted.native

hierarchicalpt.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalpt.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalpt.native

hierarchicalignorept.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalignorept.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalignorept.native

hierarchicalignoreimpactedpt.native: $(IMPACTEDML) $(IMPACTEDMLI) $(CHANGE) ocaml/hierarchicalignoreimpactedpt.ml
	$(SED) $(IMPACTEDMLI)
	$(OCAMLBUILD_JSON) hierarchicalignoreimpactedpt.native

ids.native: ocaml/ids.ml
	$(OCAMLBUILD_JSON) ids.native

neighbors.native: ocaml/neighbors.ml
	$(OCAMLBUILD_JSON) neighbors.native

$(IMPACTEDML) $(IMPACTEDMLI):
	+$(MAKE) -C ../.. extraction/impacted/$@

clean:
	$(OCAMLBUILD) -clean

.PHONY: default clean $(IMPACTEDML) $(IMPACTEDMLI)

.NOTPARALLEL: $(IMPACTEDML) $(IMPACTEDMLI)
