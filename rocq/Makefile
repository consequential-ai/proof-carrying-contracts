# The mechanization of the paper "Proof-Carrying Contracts: Commitments AI Agents Cannot Break".
# Rocq 9 with MathComp (boot) only. `make` builds the library, then checks `Paper.v`: every result it
# lists must be closed under the global context (no axiom, no admitted lemma).

all: paper

Makefile.rocq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.rocq

lib: Makefile.rocq
	$(MAKE) -f Makefile.rocq

paper: lib
	rocq c -Q PC2 PC2 -w -notation-overridden Paper.v > Paper.log
	@if grep -q '^Axioms:' Paper.log; then \
	  echo "Paper.v: some result depends on an axiom:"; grep -B1 -A3 '^Axioms:' Paper.log; exit 1; \
	fi
	@n=$$(grep -c '^Closed under the global context' Paper.log); \
	m=$$(grep -c '^Print Assumptions' Paper.v); \
	if [ "$$n" -ne "$$m" ]; then \
	  echo "Paper.v: only $$n of the $$m results are closed under the global context."; exit 1; \
	fi; \
	echo "Paper.v: $$n results, each closed under the global context (no axioms)."

clean:
	if [ -f Makefile.rocq ]; then $(MAKE) -f Makefile.rocq clean; fi
	$(RM) Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d Paper.log Paper.vo Paper.vos Paper.vok Paper.glob .Paper.aux

.PHONY: all lib paper clean
