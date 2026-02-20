tidy/%.html : html/%.html
	cat html/$*.html | htmlq .problem-box --pretty > $@

html/%.html :
	curl https://www.erdosproblems.com/$* > $@

conjectures/%.lean : tidy/%.html
	# gemini --model gemini-3-pro-preview --yolo --prompt "create formalization of conjecture described in tidy/$*.html and put in conjectures/$*.lean. do not fetch existing solutions from web."
	claude --verbose --dangerously-skip-permissions -p "create formalization of conjecture described in tidy/$*.html and put in conjectures/$*.lean. do not fetch existing solutions from web."

build-logs/%.txt : conjectures/%.lean
	lake build conjectures/$*.lean 2>&1 | tee $@

# ---------------------------------

todo-conjectures.txt : all-conjectures.txt existing-conjectures.txt
	comm -23 --nocheck-order all-conjectures.txt existing-conjectures.txt > $@

all-conjectures.txt :
	seq 1 1179 > $@

existing-conjectures.txt :
	ls ../formal-conjectures/FormalConjectures/ErdosProblems | cut -d '.' -f 1 | sort -n > $@

# ---------------------------------

.PHONY : setup
setup :
	mkdir -p html
	mkdir -p tidy
	mkdir -p conjectures
	mkdir -p reviews
	mkdir -p sessions
	mkdir -p build-logs


.PHONY : install-elan
install-elan :
	curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

.PHONY : set-path
set-path :
	# TODO - do this in bashrc or somewhere actually functional
	export PATH="$$PATH:$$HOME/.elan/bin:$$HOME/.cargo/bin"
