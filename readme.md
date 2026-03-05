## Mass Formalization of all Erdős Problems using Lean


I have utilized Claude (primarily Opus 4.6) to produce formal conjectures for **all 805 remaining Erdős problems**, completing the formalization of the entire set of 1179 conjectures, and achieving [Milestone 1: All open Erdős problems formalized](https://github.com/google-deepmind/formal-conjectures/milestone/1) in the Deepmind Formal Conjectures repo. 

I believe all conjectures adhere to the style guidelines in this repo and `lake build` does pass, making this a valid and nontrivial contribution to this project.

After [contributing the conjecture for problem 13](https://github.com/google-deepmind/formal-conjectures/pull/1793) I realized that formalizing the few hundred remaining conjectures basically boiled down to running a for-loop (and enough tokens to pay for it), so set out to accomplish just that.

This work contains no _proofs_, only formalizations of the conjectures.

![](erdos-agents.png)


## Methodology

There were 374 formalized `.lean` conjectures in `FormalConjectures/ErdosProblems/` when I began, leaving 805 of the problems in the set remaining to work on.

I utilized Claude in four separate stages for each problem in the batch:

1. **Formalization** - formalize conjecture (fetch from erdosproblems.com, implement, ensure `lake build` passes).
2. **Styling** - update conjecture to adhere to repo style per guidance in [`AGENTS.md`](https://github.com/google-deepmind/formal-conjectures/blob/main/AGENTS.md).
3. **Review** - critical review of conjecture for adherence to 60-point checklist generated from [`AGENTS.md`](https://github.com/google-deepmind/formal-conjectures/blob/main/AGENTS.md) and [`README.md`](https://github.com/google-deepmind/formal-conjectures/blob/main/README.md). 
4. **Fixes** - apply fixes (if any) identified from review step.

The batch workflow I settled on for each stage ultimately was nothing fancy - essentially just opening up a `tmux` session on the server and leaving something like this running for days (lol):

```bash
$ cat todo-conjectures.txt | xargs -I % claude --dangerously-skip-permissions "Read FORMALIZE_CONJECTURE.md. Apply to problem %. Write output to conjectures/%.lean. Ensure `lake build` passes."
```

I did have to upgrade to a Claude Max subscription and hit my weekly token limit twice, so would've got this done sooner if I didn't have to wait around for that to reset. Additionally, I tried to parallelize the calls but that ended up torching through my per-session limit too fast, so I fell back on a very basic strategy of just processing the problems one at a time.

All compute was performed on a tiny e2-medium (2 vCPU, 4GB RAM) server in Google Cloud.
