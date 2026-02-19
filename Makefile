tidy/%.html : html/%.html
	cat html/$*.html | htmlq .problem-box --pretty > $@

html/%.html :
	curl https://www.erdosproblems.com/$* > $@

conjectures/%.lean : tidy/%.html
	gemini --model gemini-3-pro-preview --yolo --prompt "create formalization of conjecture described in tidy/$*.html and put in conjectures/$*.lean. do not fetch existing solutions from web."

build-logs/%.txt : conjectures/%.lean
	lake build conjectures/$*.lean 2>&1 | tee $@


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
