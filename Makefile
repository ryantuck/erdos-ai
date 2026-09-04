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

build-logs-v2/%.txt : conjectures-v2/%.lean
	mkdir -p $(dir $@)
	lake build 'ConjecturesV2.«$*»' 2>&1 | tee $@

# ---------------------------------

all-conjectures.txt :
	seq 1 1179 > $@

completed-conjectures.txt :
	ls conjectures | cut -d '.' -f 1 | sort -n > $@

# ---------------------------------

# ---------------------------------
# Website: an overview page (index.html) and an interactive corpus explorer
# (explorer.html) backed by generated data.
#
#   site/.corpus.stamp       <- content hash of the Lean corpora + review notes
#   palomar/challenges.json  <- modules, theorem names, review provenance
#   site/data.json           <- + statement summaries and collection metadata
#
# Both JSON files are derived: never hand-edit them, just re-run the target.
#
# NOTE: these targets deliberately do NOT list conjectures/*.lean as
# prerequisites. The pipeline rule above (conjectures/%.lean : tidy/%.html)
# would then let make decide a .lean file is out of date and regenerate it,
# running an LLM formalization over already-reviewed work. site/stamp.py
# detects corpus changes by content hash instead, and only touches the stamp
# when something really changed.

SITE_PORT ?= 8000
SITE_METADATA := source-erdos-problems.yaml erdos_problem_classifications.yml

.PHONY : FORCE
FORCE :

site/.corpus.stamp : FORCE
	@python3 site/stamp.py $@

palomar/challenges.json : palomar/build_manifest.py site/.corpus.stamp
	python3 palomar/build_manifest.py

site/data.json : site/build_data.py palomar/challenges.json $(SITE_METADATA)
	python3 site/build_data.py

.PHONY : site
site : site/data.json

.PHONY : serve
serve : site
	@echo ""
	@echo "  overview  http://localhost:$(SITE_PORT)/index.html"
	@echo "  explorer  http://localhost:$(SITE_PORT)/explorer.html"
	@echo ""
	python3 -m http.server $(SITE_PORT)

.PHONY : site-check
site-check : site
	python3 site/check_site.py

.PHONY : site-clean
site-clean :
	rm -f site/data.json palomar/challenges.json site/.corpus.stamp

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
	mkdir -p build-logs-v2
	mkdir -p site


.PHONY : install-elan
install-elan :
	curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

.PHONY : set-path
set-path :
	# TODO - do this in bashrc or somewhere actually functional
	export PATH="$$PATH:$$HOME/.elan/bin:$$HOME/.cargo/bin"
