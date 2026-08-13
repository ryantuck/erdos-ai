# Archived: rules for the DeepMind restyling effort.
#
# This targeted google-deepmind/formal-conjectures, whose contributions are
# human-reviewed. That route is no longer the project's path — see ../GAME_PLAN.md
# — and nothing in the live pipeline reads from this directory.
#
# Kept runnable for reference. Run from inside deepmind/:
#
#     make -C deepmind stylized-conjectures.txt
#
# The styling rule needs a sibling ../../formal-conjectures checkout and the
# 4.27.0 toolchain; see ../SETUP_LEAN_ENV.md.

deepmind/%.lean : ../conjectures/%.lean
	claude --dangerously-skip-permissions -p "read deepmind/ADHERE_TO_DEEPMIND_STYLE.md. Apply to problem $*."

to-stylize.txt : ../completed-conjectures.txt stylized-conjectures.txt
	comm -23 --nocheck-order $^ > $@

stylized-conjectures.txt :
	ls deepmind | cut -d '.' -f 1 | sort -n > $@

# ---------------------------------

todo-conjectures.txt : ../all-conjectures.txt formalized-conjectures.txt
	comm -23 --nocheck-order $^ > $@

formalized-conjectures.txt : deepmind-conjectures.txt ../completed-conjectures.txt
	cat $^ | sort -n | uniq > $@

deepmind-conjectures.txt :
	ls ../../formal-conjectures/FormalConjectures/ErdosProblems | cut -d '.' -f 1 | sort -n > $@
