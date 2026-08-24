# Palomar: what this corpus is, and what it isn't

[Palomar](https://palomar-registry.org/) is a registry of Lean-verified
mathematics, announced by Terence Tao on 18 August 2026 and positioned as the
analogue of a preprint server for Lean proofs. This document records where this
repository stands in relation to it.

**Short version: this corpus cannot be registered on Palomar, and that is not a
defect in the corpus.** Palomar registers verified *results*. This repository
contains formalized *statements* of open problems — 1179 of them, every theorem
ending in `sorry`, because for most of these problems no proof exists to
formalize. A conjecture is not a weak submission to a proof registry; it isn't
that kind of object at all.

What this branch does instead is make the corpus a good citizen of that
ecosystem: it declares its provenance in the standard format, and it presents
its statements in the shape a solver actually needs.

## What Palomar requires

A submission is a snapshot of a public repository containing three things:

| Part | What it is |
|---|---|
| **Challenge file** | A short, human-readable Lean description of the results claimed. Theorems here carry `sorry` — the placeholder *is* the specification. |
| **Solution module** | An arbitrarily long proof of exactly those results. |
| **`formalization.yaml`** | The results in informal language, plus provenance metadata and disclosures. |

On submission it runs two checks. The first is mechanical, using
[`leanprover/comparator`](https://github.com/leanprover/comparator): the
solution module must typecheck, prove *exactly* the statements the challenge
file claims, and depend only on a permitted axiom list. Comparator rejects
`sorry` in a solution. The second check is non-deterministic — a language model
reads the informal description in `formalization.yaml` and judges whether it
matches the formal claim. A repository passing both, and meeting the registry's
minimal standards, can be registered.

> **Sourcing note.** The Comparator contract and the `formalization.yaml` schema
> below were read directly from their repositories. The description of Palomar's
> own submission flow is second-hand: `palomar-registry.org` and the announcing
> blog post are unreachable from the environment this document was written in,
> so that part is reconstructed from search results rather than quoted from the
> primary source. Verify it against the registry before acting on it. The exact
> submission mechanism — form, pull request, or API — is not established here.

## Why this corpus is ineligible

Nothing in it is proved. The promoted set — the best available statement for
each of the 1179 problems — declares 1889 theorems containing 1909 `sorry`
placeholders. There is no solution module to submit, and for the open problems
there could not be one without first solving an Erdős problem.

Two further gaps would matter even if proofs existed:

- **23 definitions in 21 problems are themselves `sorry`.** A statement
  quantifying over a definitional hole is vacuous or ill-defined regardless of
  what a proof of it would look like. All 23 are in unreviewed first-pass files;
  the reviewed second-pass corpus has none. The manifest flags every one, and
  `palomar/make_config.py` warns when you ask for an affected problem.
- **909 of 1179 problems have never been adversarially reviewed.** Of the 270
  that have, 93 needed semantic corrections — wrong polarity, vacuity, misplaced
  quantifiers. Assume the unreviewed remainder carries defects at a similar rate.

## What the corpus is: the challenge half

Comparator's challenge file is precisely "theorems with `sorry` that specify what
must be proven." That is what every file here already is. The scarce input to a
proof registry is not proofs alone but *faithful statements* — and faithfulness
is exactly what this project's adversarial second pass measures.

So this branch ships the corpus in usable challenge form:

```
palomar/
├── challenges.json      # all 1179 problems → module, theorem names, provenance
├── build_manifest.py    # regenerates challenges.json from the repo
├── make_config.py       # emits a Comparator config for any problem
└── configs/             # three worked examples (88, 89, 90)
```

To attempt a problem, write a solution module proving the named theorems and
generate the config:

```bash
python3 palomar/make_config.py 89 --solution MySolution -o /tmp/89.json
```

which yields

```json
{
  "challenge_module": "ConjecturesV2.«89»",
  "solution_module": "MySolution",
  "theorem_names": ["erdos_problem_89", "..."],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
```

Then run Comparator against it. Each manifest entry also carries the problem's
review verdict, whether its statement came from the reviewed or unreviewed pass,
and any definitional caveats — so you can tell before starting whether the
statement you are about to prove has been checked by anyone.

**These configs have not been executed.** This repository has no Lean toolchain
installed, and the project's standing practice is to defer all compile
verification to a machine that has one. The module-name spelling in particular
(`ConjecturesV2.«89»`, following the `lake build` target form) is untested
against Comparator. Treat the configs as unverified until you run them.

## What would make a real Palomar submission

One route only: prove something. A handful of Erdős problems are resolved and
have short enough published proofs to formalize — that would produce a genuine
registrable result, with this corpus's statement as its challenge file. It would
be a different project from this one, and the other 1178 statements would not
come along with it.

Two adjacent destinations fit the corpus as it stands:

- **[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)**
  is where a formalized conjecture *is* the contribution. 805 of these problems
  were written for it, completing its "all open Erdős problems formalized"
  milestone.
- **[leanprover/lean-eval](https://github.com/leanprover/lean-eval)** is a
  Comparator-based evaluation built on exactly this shape — `@[eval_problem]`
  theorems ending in `sorry`, one manifest per problem. A reviewed,
  provenance-tracked corpus of Erdős statements is a substantial input to it.

## `formalization.yaml`

The repository root carries a
[`formalization.yaml`](formalization.yaml) conforming to v0.4 of the
[mathlib-initiative standard](https://github.com/mathlib-initiative/formalization.yaml).
That standard is a self-reporting format for autoformalization projects and
applies here regardless of registration eligibility — it has fields for exactly
the things this project needs to disclose: which models produced what, how the
work was reviewed, and where the formalization diverges from its sources.

It validates cleanly:

```bash
check-jsonschema --schemafile \
  https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json \
  formalization.yaml
```

Two entries there deserve highlighting, because they are where an
autoformalization project is most tempted to flatter itself:

- **`review.status: agent-reviewed`**, not `peer-reviewed`. No human has reviewed
  this corpus. The reviewers are named as models, with the problem ranges each
  covered.
- **`fidelity.divergences`** records the defect taxonomy honestly, including that
  no formalization has ever come back clean from review, and that 909 problems
  have not been looked at.

`status.sorry_count` is `0` because the standard defines that field to exclude
"the deliberate placeholder sorry in a Comparator challenge module," which is
what every `sorry` here is. The raw count of 1909 is stated in `status.scope` so
that the zero cannot be mistaken for a claim that the corpus contains proofs.
