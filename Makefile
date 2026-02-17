tidy/%.html : html/%.html
	cat html/$*.html | htmlq .problem-box --pretty > $@

html/%.html :
	curl https://www.erdosproblems.com/$* > $@

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
