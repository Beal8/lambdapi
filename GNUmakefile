OCAMLBUILD = ocamlbuild -use-ocamlfind -quiet
BINDIR     = $(dir $(shell which ocaml))
VIMDIR     = $(HOME)/.vim

#### Compilation #############################################################

.PHONY: all
all: lambdapi.native

lambdapi.native: _build/src/lambdapi.native

_build/src/lambdapi.native: $(wildcard src/*.ml)
	$(OCAMLBUILD) src/lambdapi.native

#### Unit tests ##############################################################

OK_TESTFILES = $(wildcard dedukti_tests/OK/*.dk)
KO_TESTFILES = $(wildcard dedukti_tests/KO/*.dk)
TESTFILES    = $(wildcard tests/*.dk) \
							 $(wildcard examples/*.dk) \
							 $(wildcard other_examples/*.dk)

.PHONY: tests
tests: lambdapi.native
	@echo "## OK tests ##"
	@rm -f $(OK_TESTFILES:.dk=.dko)
	@for file in $(OK_TESTFILES) ; do \
		echo -n "Testing file \"$$file\" " ; \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;32mOK\033[0m" || echo -e "\033[0;31mKO\033[0m" ; \
	done
	@echo "## KO tests ##"
	@rm -f $(KO_TESTFILES:.dk=.dko)
	@for file in $(KO_TESTFILES) ; do \
		echo -n "$$file " ; \
		./lambdapi.native --verbose 0 $$file 2> /dev/null \
		  && echo -e "\033[0;31mOK\033[0m" || echo -e "\033[0;32mKO\033[0m" ; \
	done
	@echo "## Tests... ##"
	@rm -f $(TESTFILES:.dk=.dko)
	@for file in $(TESTFILES) ; do \
		echo "$$file" ; \
		./lambdapi.native --verbose 0 $$file ; \
	done

#### Library tests ###########################################################

.PHONY: matita
matita: lambdapi.native
	@echo "## Compiling the Matita's arithmetic library ##"
	@cd libraries && ./matita.sh

.PHONY: focalide
focalide: lambdapi.native
	@echo "## Compiling focalide library ##"
	@cd libraries && ./focalide.sh

.PHONY: holide
holide: lambdapi.native
	@echo "## Compiling holide library ##"
	@cd libraries && ./holide.sh

.PHONY: verine
verine: lambdapi.native
	@echo "## Compiling verine library ##"
	@cd libraries && ./verine.sh

.PHONY: iprover
iprover: lambdapi.native
	@echo "## Compiling iProverModulo library ##"
	@cd libraries && ./iprover.sh

.PHONY: dklib
dklib: lambdapi.native
	@echo "## Compiling the dklib library ##"
	@cd libraries && ./dklib.sh

#### Cleaning targets ########################################################

.PHONY: clean
clean:
	@ocamlbuild -clean

.PHONY: distclean
distclean: clean
	@cd libraries && ./matita.sh clean
	@cd libraries && ./focalide.sh clean
	@cd libraries && ./holide.sh clean
	@cd libraries && ./iprover.sh clean
	@cd libraries && ./verine.sh clean
	@cd libraries && ./dklib.sh clean
	@find . -type f -name "*~" -exec rm {} \;
	@find . -type f -name "*.dko" -exec rm {} \;

#### Installation targets ####################################################

# Install the main program.
.PHONY: install
install: lambdapi.native
	install -m 755 $^ $(BINDIR)

# Install for the vim mode (in the user's directory).
.PHONY: install_vim
install_vim: editors/vim/ftdetect/dedukti.vim editors/vim/syntax/dedukti.vim
ifeq ($(wildcard $(VIMDIR)/.),)
	@echo -e "\e[36mWill not install vim mode.\e[39m"
else
	install -d $(VIMDIR)/syntax
	install -d $(VIMDIR)/ftdetect
	install -m 644 editors/vim/syntax/dedukti.vim $(VIMDIR)/syntax
	install -m 644 editors/vim/ftdetect/dedukti.vim $(VIMDIR)/ftdetect
	@echo -e "\e[36mVim mode installed.\e[39m"
endif
