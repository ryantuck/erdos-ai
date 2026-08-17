---
batch: 1-90
reviewer_model: claude-fable-5
review_dates: 2026-08-16..2026-08-17
input_artifacts: conjectures/1.lean .. conjectures/90.lean
output_artifacts: conjectures-v2/N.lean, fable-review/N.md (N = 1..90)
problems_reviewed: 90
verdict_accept: 0
verdict_accept_with_nits: 69
verdict_needs_revision: 21
confidence_high: 11
confidence_medium: 79
confidence_low: 0
source_recovered: 90
compile_status: pending
batch_complete: false
not_reviewed: 91-100
halt_reason: usage-limit
---

# Fable review batch 1–90

Adversarial review of the Lean formalizations in `conjectures/1.lean` … `conjectures/90.lean`
against recovered primary sources, per `FABLE_REVIEW_RUN.md`. One reviewer agent per problem,
each writing exactly two files (`conjectures-v2/N.lean`, `fable-review/N.md`) and leaving
`conjectures/N.lean` untouched. Every review was performed by `claude-fable-5`.

**This batch is incomplete: problems 91–100 were not reviewed.** See
[Usage limits and what they cost](#usage-limits-and-what-they-cost) below.

## Headline numbers

| Metric | Value |
|---|---|
| Problems reviewed | 90 of 100 |
| ACCEPT | 0 |
| ACCEPT WITH NITS | 69 |
| NEEDS REVISION | 21 |
| Confidence high / medium / low | 11 / 79 / 0 |
| Source recovered from primary capture | 90 / 90 |
| Compile-verified | 0 (deferred to `lake build` on the maintainer's machine) |

No formalization earned a plain ACCEPT. Every file needed at least documentation work —
most commonly a missing verbatim problem statement, absent status/provenance, or
unkeyed citations. Confidence is capped at `medium` by design whenever anything is
DEFERRED, and the no-compiler constraint plus incomplete bibliographies put nearly every
review in that bucket.

Source recovery was 90/90: no review relied on the model's own recollection of a problem
statement. Statements came from archived page captures (in-repo `tidy/N.html`, or
`WebFetch` results preserved in session logs), with status cross-checked against the
`teorth/erdosproblems` mirror's `data/problems.yaml` and the upstream
`google-deepmind/formal-conjectures` HEAD.

## NEEDS REVISION (21)

| # | Defects |
|---|---|
| 1 | degenerate-case-falsity |
| 2 | missing-distinctness-hypothesis, trivially-false-statement |
| 7 | missing-modulus-gt-one-hypothesis, trivially-true-statement |
| 8 | missing-distinctness-hypothesis, missing-modulus-lower-bound, trivially-false-statement |
| 10 | answer-polarity |
| 20 | degenerate-case-falsity, undefined-citation-key, missing-citation, misattributed-bound |
| 25 | unconstrained-optparam-binder, trivially-false-statement |
| 32 | missing-problem-part |
| 33 | liminf-junk-value |
| 34 | wrong-polarity |
| 36 | trivially-true-statement, optimality-dropped |
| 40 | overstrong-quantifier, trivially-false-statement |
| 43 | wrong-polarity, missing-part |
| 50 | unconstrained-derivative-domain, trivially-false-statement |
| 55 | constant-quantifier-order |
| 56 | wrong-polarity, def-docstring-mismatch |
| 59 | wrong-polarity |
| 64 | polarity-belief-contradiction |
| 78 | false-at-small-parameter, missing-citation |
| 80 | false-at-small-parameter, missing-citation |
| 90 | refuted-direction-asserted, false-at-small-cardinality, missing-citation-key |

Defects were also found in five files whose overall verdict stayed at ACCEPT WITH NITS
because the defect was documentation-level or non-semantic: 45, 65, 70, 76 (citation
problems) and 86 (a compile-blocking syntax defect, fixed).

## Defect taxonomy

Aggregated from the `defects:` front-matter field across all 90 reviews:

| Class | Count |
|---|---|
| missing-citation / missing-citation-key | 7 |
| undefined-citation-key | 5 |
| trivially-false-statement | 5 |
| wrong-polarity / answer-polarity / polarity-belief-contradiction / refuted-direction-asserted | 7 |
| trivially-true-statement | 2 |
| missing-distinctness-hypothesis | 2 |
| false-at-small-parameter / false-at-small-cardinality | 3 |
| degenerate-case-falsity | 2 |
| missing-problem-part / missing-part | 2 |
| everything else (one occurrence each) | 11 |

The three dominant families, and what they look like in practice:

**Polarity (7 occurrences).** The formalization asserts the direction of a question that
the source records as refuted, or drops the `answer(False)` wrapper on a disproved
problem. This is the highest-severity class in the corpus: the artifact states something
false while looking entirely well-formed. Problem 90 is the clearest instance — the unit
distance conjecture ($500 prize) was disproved in May 2026, months after the archived page
capture was taken, and the formalization asserted it positively. Problem 64 is subtler: the
statement contradicted the belief the same file's docstring attributed to Erdős.

**Vacuity and degeneracy (12 occurrences across trivially-true, trivially-false,
degenerate-case, and small-parameter classes).** A statement that is provable or refutable
for reasons having nothing to do with the mathematics. Recurring mechanisms found in this
batch: Mathlib junk values at degenerate inputs (`Real.log 0 = 0`, `sInf ∅ = 0`,
`rpow 0 0 = 1`, `φ(0) = 0`, `minDegree ∅ = 0`); `log log n < 0` for small `n` making an
asymptotic bound literally false there (problem 90); an unconstrained `optParam` default
binder letting a caller instantiate a def outside its intended domain (problem 25); an
`∃ c` positioned so that any positive constant satisfies it (problem 36); and a constant
quantified inside a `∀`-parameter, so it can absorb the very factor the problem is about
(problem 55).

**Bibliography (12 occurrences).** Citation keys used in docstrings but defined nowhere,
references with no bibliographic data, and — in one case — a bound attributed to the wrong
paper (problem 20). Reviews were required to produce honest stubs rather than plausible
guesses; where sibling files in the repo disagreed about an expansion, nothing was imported.

## Notable findings

**Problem 90 — a conjecture disproved after the page capture.** The mirror's
`problems.yaml` records "disproved (Lean)" as of 2026-06-07 and upstream states
`answer(False)`, citing Sawin (arXiv:2605.20579) and a nine-author "Remarks" paper
(arXiv:2605.20695) following a construction found by an internal OpenAI model. The archived
page still shows the OPEN banner. Beyond negating the statement, the review found that
naively negating it would have been *trivially* satisfiable by a two-point witness (where
`log log 2 < 0` makes the bound false regardless of the constant) — so the small-cardinality
guard is load-bearing: without it, the "fixed" file would look like a disproof while
proving nothing.

**Problem 86 — an empirically compile-blocking pattern.** `loopless := ⟨fun …⟩` fails to
elaborate against `SimpleGraph`'s Pi-type `Irreflexive Adj` field; the bare lambda is the
form that builds. This was established from archived `lake build` transcripts, not
guessed. The same pattern was then found and fixed in three earlier output files
(`conjectures-v2/60.lean`, `65.lean`, `1105.lean`) in a separate cross-cutting commit —
the only edit in this batch that touched files outside its own problem's pair.

**Problem 85 — "unused" imports can be load-bearing.** An import that no identifier in the
file references may still be supplying an instance or a simp lemma. Import removal now
requires a transitive-reachability check.

**Brute-force simulation caught helper-definition bugs.** Several reviews (56, 77, 79,
81–85, 88) numerically enumerated small cases rather than reading the definition and
agreeing with it. Problem 56's helper def was right by count and wrong by elements — a
defect that reading alone had missed and that only simulation settled.

**Recent-resolution drift is systemic in this range.** Problems 38 and 42 were solved by
GPT 5.5 Pro; 45, 69, 76, 79 solved; 43 and 56 disproved; 71 machine-verified; 90 disproved.
Archived captures are stale on all of these. Status must come from the mirror and upstream
HEAD, never from the captured banner alone.

## Audit of the prior review pass

Each review re-derived the claims in the corresponding `deepmind/ai-review/N.md` where one
exists (none exists for 89 or 90; those Part E sections were skipped explicitly rather
than invented). Recurring failure modes in that prior pass:

- **Fabricated or wrong-paper citations certified as verified** (16, 18, 21, 31, 52, 71,
  72, 76, 84, 88). Problem 88's is representative: the prior review certified that a
  journal citation "matches the website", where the authoritative source cites only an
  arXiv preprint. It also asserted a $100 prize "was awarded" where captures show only
  "PROVED - $100".
- **Right conclusion, unsound argument** (87, 88, and the same pattern in the earlier
  1000/1005 audits). Problem 87's prior review justified an `ε < 1` restriction with
  "for ε ≥ 1, (1−ε)^k ≤ 0, so trivially satisfied" — false for even `k`, where the
  unrestricted statement is provably false rather than trivially true.
- **Unsound "critical fixes"** (79). A proposed size-Ramsey correction would have
  introduced a misformalization; it was rejected with the reasoning recorded.
- **Flagged but never backported** (50, 70, 80). Defects correctly identified in the prior
  pass were fixed only in styled copies, never in the artifacts under review.

## Usage limits and what they cost

The batch halted at 90 of 100 because the account's usage allowance was exhausted, twice.

**First hit (problems 9 and 10).** Both in-flight reviewer agents died with "You're out of
usage credits". No partial files were left on disk. Recovery: confirm the working tree is
clean, confirm problems 1–8 were all committed (problem 7's commit had landed moments
before the outage), then relaunch 9 and 10 once the allowance reset, passing each dead
agent's salvaged partial findings into the relaunch prompt.

**Second hit (problems 91 and 92).** Same failure, same clean-tree outcome. The relaunched
pair ran under a different model tier, which would have made the batch's provenance
heterogeneous, so those two reviews were stopped before writing anything and the batch is
being closed at 90 rather than mixed. Salvaged findings worth carrying forward to whoever
resumes:

- **Problem 91**: the `/latex/91` bibliography extraction is recoverable from the session
  logs; the open questions were whether the session captured `[Er97e]` details, what the
  styled deepmind copy contains, and whether upstream has a 91 file.
- **Problem 92**: upstream records *both* of problem 92's questions as `answer(False)` —
  refuted as a consequence of problem 90's disproof. Expect the same
  `refuted-direction-asserted` defect the review of 90 found, and check that any negation
  is not trivially satisfiable by a degenerate witness.

**A separate, unrelated failure mode worth documenting:** agents sometimes die *silently* —
no completion notification, no error, no files, and the fleet listing simply shows nothing
running. This happened to problems 76 and 77 and went unnoticed until the maintainer asked
why nothing was running. A liveness check at every commit checkpoint is now standard;
a scheduled watchdog would be better but requires an approval this environment does not
grant.

### Cost profile and how to run this cheaper

Reported per-review token usage for the four most recent problems ran 106k–144k, averaging
roughly 127k. At that rate a 100-problem batch costs on the order of 12M tokens, which is
what exhausted the allowance. Concretely, for future batches:

1. **Trim mandated reading.** Each agent reads `FABLE_REVIEW_RUN.md` and
   `FABLE_REVIEW.md` in full before touching the problem. That is a fixed per-problem tax
   paid 100 times. A condensed operative checklist, with the rationale kept in a document
   agents are told about but not required to read, would cut it substantially.
2. **Pre-extract sources once, centrally.** Recovering an archived page from session logs
   costs several greps and a large read per problem, and each agent rediscovers the same
   log-layout facts. Extracting `tidy/N.html` for a whole batch up front, in one pass,
   removes that work from the per-problem loop entirely.
3. **Two-tier review.** A cheaper model can do the scaffolding — recover the page, write
   the docstring, key the citations, fill the front matter — leaving the frontier model
   only the mathematical pass (polarity, vacuity, quantifier order, small-case
   simulation). The Haiku benchmark on problems 1101–1179 (see PR #11) showed a cheap
   model catches convention-level issues reliably at roughly half the tokens, while
   missing the semantic defects and fabricating citations — which is exactly the split
   this tiering assumes.
4. **Don't raise parallelism to go faster.** Concurrency does not reduce total tokens; it
   only reaches the ceiling sooner. Two agents in flight remains the right setting.
5. **Batch the cross-cutting sweeps.** The `optParam` scan (problem 25) and the `loopless`
   scan (problem 86) each found instances corpus-wide in a single grep. Running the known
   defect-pattern greps once per batch is far cheaper than rediscovering each pattern
   inside an individual review.

## Verification still outstanding

Nothing in `conjectures-v2/` has been compiled. Per `GAME_PLAN.md`, `lake build`
verification is deferred to the maintainer's machine; all 90 reviews carry
`compile_status: pending`. Variants added with `sorry` bodies are flagged as
not-compile-verified in their own files. Bibliographic data marked DEFERRED in individual
reviews remains unresolved — the `/latex/N` extractions were unavailable in the session
logs for a substantial fraction of the batch, and no expansion was invented to fill a gap.

## Carry-forward for later batches

- `conjectures/486.lean` carries the same unconstrained-`optParam` defect as problem 25.
- Problems 91–100 are unreviewed; salvaged findings for 91 and 92 are above.
- Upstream `formal-conjectures` bugs documented in individual reviews and not yet reported
  upstream: problem 15's provably-false `Summable` encoding, problem 11's Wieferich
  polarity, problem 12's `=O[atTop]` versus infinitely-many, problem 41's B₃ `a+a+b`
  collision gap.
