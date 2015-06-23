COQC=coqc
COQFLAGS=
COQDEP:=$(COQBIN)coqdep -c
GALLINA:=$(COQBIN)gallina
COQDOC:=$(COQBIN)coqdoc
COQMKTOP:=$(COQBIN)coqmktop
COQLIBS:=-I . 


VFILES:=SfLib.v SystemFC.v Shifting.v Substitution.v Typing.v Evaluation.v\
   SubstProp.v SystemFCProp.v

VOFILES:=$(VFILES:.v=.vo)
VOFILES0:=$(filter-out ,$(VOFILES))
GLOBFILES:=$(VFILES:.v=.glob)
VIFILES:=$(VFILES:.v=.vi)


####################
#                  #
# Special targets. #
#                  #
####################

all: $(VOFILES)

spec: $(VIFILES)

.PHONY: all opt byte archclean clean install depend html

vo: $(VOFILES)

SystemFC.vo: SfLib.vo
Shifting.vo: SystemFC.vo
Substitution.vo: Shifting.vo
Typing.vo: Substitution.vo
Weakening.vo: Typing.vo
Evaluation.vo: Substitution.vo Typing.vo
SubstProp.vo: Typing.vo Evaluation.vo Weakening.vo
Consistency.vo: Typing.vo SubstProp.vo 
SystemFCProp.vo: Consistency.vo


%.vo %.glob: %.v 
	$(COQC) $*

%.vi: %.v Makefile
	$(COQC) -i $(COQFLAGS) $*


printenv: 
	@echo CAMLC =	$(CAMLC)
	@echo CAMLOPTC =	$(CAMLOPTC)
	@echo CAMLP4LIB =	$(CAMLP4LIB)

byte:
	$(MAKE) all "OPT:=-byte"

opt:
	$(MAKE) all "OPT:=-opt"

clean:
	rm *.vo *.glob

archclean:
	rm -f *.cmx *.o



-include $(VFILES:.v=.v.d)
.SECONDARY: $(VFILES:.v=.v.d)

include .depend
