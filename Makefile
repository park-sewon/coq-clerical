DUNE=dune

default: clerical.exe

COQMAKEFILE = coq_makefile
COQSRC = formalization

.PHONY: coq_code clean

### Compilation of Coq files

$(COQSRC)/Makefile: $(COQSRC)/_CoqProject
	cd $(COQSRC) && $(COQMAKEFILE) -f _CoqProject

coq_code: $(COQSRC)/Makefile
	$(MAKE) -C $(COQSRC)

# Cleaning up

clean: $(COQSRC)/Makefile
	$(MAKE) -C $(COQSRC) clean
