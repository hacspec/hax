EXAMPLES_HOME=$(realpath ..)
include $(EXAMPLES_HOME)/Makefile.include

all:
	rm -f .depend && $(MAKE) .depend
	$(MAKE) verify


# By default, we process all the files in the current directory. Here, we
# *extend* the set of relevant files with the tests.
ROOTS = $(wildcard *.fst)
