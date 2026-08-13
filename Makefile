# Live pipeline: erdosproblems.com/N -> conjectures/N.lean -> fable review ->
# conjectures-v2/N.lean. See GAME_PLAN.md.
#
# The DeepMind restyling effort is archived; its rules live in deepmind/Makefile.

tidy/%.html : html/%.html
	cat html/$*.html | htmlq .problem-box --pretty > $@

html/%.html :
	curl https://www.erdosproblems.com/$* > $@

conjectures/%.lean : tidy/%.html
	claude --verbose --dangerously-skip-permissions -p "read FORMALIZE_CONJECTURE.md. Formalize conjecture number $*."

build-logs/%.txt : conjectures/%.lean
	lake build conjectures/$*.lean 2>&1 | tee $@

# ---------------------------------

all-conjectures.txt :
	seq 1 1179 > $@

completed-conjectures.txt :
	ls conjectures | cut -d '.' -f 1 | sort -n > $@

# ---------------------------------

.PHONY : setup
setup :
	mkdir -p html
	mkdir -p tidy
	mkdir -p conjectures
	mkdir -p conjectures-v2
	mkdir -p fable-review
	mkdir -p sessions
	mkdir -p build-logs


.PHONY : install-elan
install-elan :
	curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

.PHONY : set-path
set-path :
	# TODO - do this in bashrc or somewhere actually functional
	export PATH="$$PATH:$$HOME/.elan/bin:$$HOME/.cargo/bin"
