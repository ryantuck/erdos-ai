---
batch: 0091-0120
reviewer_model: claude-opus-5-5
effort: max
review_date: 2026-10-02 to 2026-10-03
selection: problems 91–120, a contiguous range chosen by the user
input_artifacts: conjectures/91.lean .. conjectures/120.lean
output_artifacts: conjectures-v2-opus-5-5/N.lean, opus-5-5-review/N.md (N = 91..120)
problems_reviewed: 30
verdict_accept: 0
verdict_accept_with_nits: 16
verdict_needs_revision: 14
confidence_high: 22
confidence_medium: 8
confidence_low: 0
source_recovered: 30
compile_status: pass
---

[AI - Claude Opus 5.5]: Opus 5.5 review batch 0091–0120

# Opus 5.5 review batch 0091–0120

This batch reviews problems 91–120 with the repository's pipeline (`FABLE_REVIEW.md` and
`FABLE_REVIEW_RUN.md`), run at **effort = max**.

- **Order.** Problems were reviewed one at a time, in numerical order. Each was committed
  separately (subject `Opus 5.5 review N: …`) and pushed before the next one started.
- **Outputs.** The inputs in `conjectures/` are untouched. The fixed files are in
  `conjectures-v2-opus-5-5/`, and the reviews are in `opus-5-5-review/`.
- **Independence.** No Fable or Haiku review exists for any of these 30 problems, so this
  batch has no cross-reviewer comparison. The only earlier reviews are the archived
  `deepmind/ai-review/N.md` files, which Part E audits.
- **Compiled.** Unlike batch 1101–1110, everything here is compile-verified. Lean 4.28.0
  and Mathlib `v4.28.0` were built from source in the container. All 30 inputs and all 30
  v2 files compile.

## Headline numbers

| Metric | Value |
|---|---|
| ACCEPT / ACCEPT WITH NITS / NEEDS REVISION | 0 / 16 / 14 |
| Confidence high / medium / low | 22 / 8 / 0 |
| Source page recovered | 30/30 (page captures in the session logs) |
| Main statements **false as written** | 9: 92, 97, 100, 105, 106, 110, 113, 115, 117 |
| Statements vacuous, mis-targeted or ill-defined | 112 (vacuous), 111 (wrong target), 99 and 100 (`sorry` in definitions), 103 (`ncard` junk value) |
| Wrong polarity | 5: 92, 105, 106, 110, 113. In 105, 110 and 113 the theorem contradicts its own docstring |
| Inputs with a citation defect | 30/30: 20 cite keys they never define, 10 cite nothing |
| Theorems: inputs → v2 | 32 → 135 (the extra 103 are page-recorded variants) |
| v2 compile | 30/30 with 0 errors, one `sorry` warning per theorem, no other warnings |

## Per-problem results

"Exact" means the main statement was judged a faithful encoding and kept byte-identical.

| # | Verdict | Conf. | Part A finding | Other findings |
|---|---|---|---|---|
| 91 | NITS | med | none; exact (non-similar distance minimisers) | no references at all |
| 92 | **NEEDS REV** | med | max–min $f(n)$ encoded pointwise, which is trivially false; false at $\lvert A\rvert=2$ ($\log\log2<0$); wrong polarity after the May 2026 disproof via #90 | \$500 question missing; 4 undefined keys |
| 93 | NITS | high | none; exact (Altman $\lfloor n/2\rfloor$) | `[Al63]` undefined |
| 94 | NITS | high | none; exact (convex $\sum f(u)^2\ll n^3$) | `[LeTh95]` undefined; "Theile" corrected to Thiele |
| 95 | NITS | high | none; exact ($\ll_\varepsilon n^{3+\varepsilon}$) | no references |
| 96 | NITS | high | none; exact (Erdős–Moser $O(n)$) | no references |
| 97 | **NEEDS REV** | high | false at $P=\emptyset$: it is vacuously in convex position, then a vertex is demanded | 8 undefined keys |
| 98 | NITS | high | none; exact ($h(n)/n\to\infty$) | no references |
| 99 | **NEEDS REV** | high | `by sorry` inside `minPairwiseDist` and `diameter` | 3 undefined keys |
| 100 | **NEEDS REV** | high | `by sorry` inside `diameter'`; false at $\lvert A\rvert=1$ | 4 undefined keys; the page's Kanold bound needs a constant |
| 101 | NITS | high | none; exact ($o(n^2)$ four-point lines) | no references |
| 102 | NITS | high | none; exact ($h_c(n)\to\infty$) | no references |
| 103 | **NEEDS REV** | med | `Set.ncard` sends infinitely many congruence classes to 0 ("rattlers"; recalled $n=8$ example) | no references |
| 104 | NITS | med | none; exact ($o(n^2)$ unit circles) | no references; `[Er83b]` DEFERRED |
| 105 | **NEEDS REV** | high | asserts the refuted "yes" while its docstring says DISPROVED | no references |
| 106 | **NEEDS REV** | med | wrong polarity after a post-capture disproof ($f(k^2+1)=k$) | no references; Halász's range restricted |
| 107 | NITS | high | none; exact (Happy Ending, both halves) | 12 undefined keys |
| 108 | NITS | med | none; exact (girth and chromatic number) | undefined keys; `[Er79b]` DEFERRED |
| 109 | NITS | high | none; exact (Erdős sumset conjecture) | `[ErGr80]` undefined |
| 110 | **NEEDS REV** | high | asserts the conjecture refuted in ZFC [La20], against its own docstring | undefined keys; Komjáth now co-credited |
| 111 | **NEEDS REV** | high | formalizes the [Er81] remark, not the page's question $h_G(n)/n\to\infty$ | undefined keys |
| 112 | **NEEDS REV** | high | `Digraph` allows 2-cycles, so `dirRamseyNum = sInf ∅ = 0` and the bound is vacuous; a known bound is labelled as the conjecture | undefined keys |
| 113 | **NEEDS REV** | high | asserts the biconditional that Janzer refuted, against its own docstring | undefined keys; #146's refutation now breaks the other direction too |
| 114 | NITS | high | none; exact (lemniscate length) | `[EHP58]` undefined; "unique up to rotation" omitted translation |
| 115 | **NEEDS REV** | high | `p.Monic` missing; the Chebyshev polynomial $T_n$ refutes the bound | undefined keys |
| 116 | **NEEDS REV** | high | `area := μH[2]` is $\frac4\pi\times$ Lebesgue measure, which leaves the theorem true but breaks Pólya's $\pi$ | undefined keys; $(\log n)^{-O(1)}$ part missing |
| 117 | **NEEDS REV** | high | Pyber's bounds asserted for every $n\ge1$, but $h(1)=h(2)=1$ | undefined keys |
| 118 | NITS | high | none; exact (partition ordinals, negated) | 9 undefined keys; Larson credited with Schipperus–Darby's result |
| 119 | NITS | med | none; exact (all three parts, "yes" direction) | undefined keys; part (iii) solved after capture (DEFERRED) |
| 120 | NITS | med | none; exact (Erdős similarity problem) | undefined keys; 3 references DEFERRED |

NITS is short for ACCEPT WITH NITS. Every v2 file also adds page-recorded variants: known
bounds, constructions, sub-questions, and the true direction of refuted strengthenings. Each
variant is labelled PROVED, OPEN or DISPROVED with its source.

## Defect classes

| Class | Count | Problems |
|---|---|---|
| undefined-citation-key | 20 | 92–94, 97, 99, 100, 107–120 |
| missing-references | 10 | 91, 95, 96, 98, 101–106 |
| wrong-polarity | 5 | 92, 105, 106, 110, 113 |
| false-at-small-parameters | 4 | 92, 97, 100, 117 |
| sorry-in-definition | 2 | 99, 100 |
| missing-part | 2 | 92, 116 |
| wrong-quantifier-structure | 1 | 92 |
| ncard-infinite-junk | 1 | 103 |
| wrong-target-statement | 1 | 111 |
| vacuous-definition | 1 | 112 |
| known-result-as-open-problem | 1 | 112 |
| missing-normalization | 1 | 115 |
| def-docstring-mismatch | 1 | 116 |
| misleading-docstring-remark | 1 | 114 |
| misattributed-result | 1 | 118 |

The two citation labels follow one convention. `undefined-citation-key` means keys are
cited but never defined; `missing-references` means nothing is cited at all.

Three patterns stand out:

- **Self-contradicting files (105, 110, 113).** The docstring records the disproof, but the
  theorem asserts the refuted statement. The raw corpus asserts the asked direction while a
  problem is open, and the true direction once it is refuted. These three files were
  written after the refutation, yet still assert the asked direction.
- **Degenerate inputs at the boundary (97, 100, 117).** Each statement quantifies over a
  range including a trivial case, such as the empty set, a single point, or $n=1,2$, where
  the conclusion fails.
- **Junk values (103, 112).** `Set.ncard` of an infinite set and `sInf ∅` are both $0$. In
  both files that silently changes the statement's meaning.

## Status changes after capture

Captures date from 2026-02-19 to 2026-03-05. The mirror snapshot is `b916d95`
(2026-09-28), and upstream `formal-conjectures` is at `df3f12d` (2026-10-01).

| # | At capture | Now | Effect on the input |
|---|---|---|---|
| 92 | OPEN | disproved (mirror 2026-05-21), via #90 (unit distances) | the asked direction is now refuted: polarity defect |
| 106 | FALSIFIABLE | `disproved (Lean)` (mirror `7b7132c`, 2026-08-31) | the asked direction is now refuted: polarity defect |
| 110 | NOT PROVABLE (already stale) | `disproved` (mirror 2026-04-05) | the input asserted the refuted direction anyway |
| 113 | DISPROVED | unchanged, but #146 is now disproved (`be86208`, `7b7132c`) | both directions of the biconditional now fail; recorded as a variant |
| 119 | OPEN (part iii) | `solved` (`cfe07e4`, 2026-07-19), then `solved (Lean)` | the "yes" direction is unchanged; the status label is updated |

The 2026 results behind 92, 106, 113 and 119 could not be read in this container. v2
records them with provenance and labels them unverified. Where they decide a verdict (92,
106), confidence is medium.

## Prior-review audit (`deepmind/ai-review/`)

21 of the 30 problems have an archived prior review. 92, 97, 99, 100, 107, 108, 109, 119 and
120 have none. Every prior review was written against a styled copy in
`deepmind/deepmind/`, never against the raw `conjectures/` file reviewed here.

**Fixes that never reached the raw corpus.** In three problems the prior review found (or
recommended the cure for) a Part A defect, and commit `2d5425c0` fixed it in the styled copy.
The raw file kept the defect:

- 112: the missing `antisymm`;
- 115: the missing `p.Monic`;
- 116: `μH[2]` instead of `volume`.

Likewise, references added to styled copies were never copied back. That is why all 30 raw
files have citation defects.

**Hallucinated or wrong bibliographic data**, some of it then written into styled copies:

- 91: an invented [Er87b] title, and a wrong claim that the page spells the author
  "Kovacs".
- 98: "Roth" invented as a co-author of [EFPR93]. The real co-author is Ruzsa.
- 105: an invented [ErPu95] title.
- 114: "Vayman (1999)" for [Va99], the "Various" Budapest booklet. Commit `2d5425c0` copied
  it into the styled copy.
- 117: the styled copy first invented "Vadász, *On the commuting properties of finite
  groups*". The review suggested "Varopoulos", and `2d5425c0` wrote that in instead.
- 118: the review certified as accurate the styled copy's four scrambled Erdős titles and a
  wrong [La00] paper.

Both "Vayman" and "Varopoulos" first appear in WebFetch summaries of the problem pages,
which expanded the key `Va99` into an author name. The site's own `/latex` bibliography
gives "Various".

**Mathematical errors:**

- 94: the logical direction of Lefmann–Thiele is reversed.
- 102: the status of an upper bound is wrong, and the link to #101 is garbled.
- 103: the `ncard` problem is dismissed.
- 104: a proposed variant is vacuous (`∃ C, C > 0 → …`).
- 106: an attainment claim is unjustified, and a range is misattributed.
- 110 and 111: false claims of set-theoretic absoluteness.
- 111: the wrong target is endorsed, and a false implication from #74 to #111 is asserted.
- 115: Chebyshev sharpness is miscomputed. As a result, the styled copy deleted a correct
  sentence.
- 116: $\mu H[2]$ is claimed, twice, to equal Lebesgue measure.
- 117: the statement's falsity at $n=1,2$ is missed, and `erdosH 0` is mis-analysed.

**Superseded:** 113's "the → direction is still open" was true in March 2026, but #146 has
since been refuted.

The prior reviews' core encoding checks were usually right: polarity of the styled copies,
`sInf`/`sSup` boundedness, and coercions.

## Compile verification

- **Toolchain.** Lean 4.28.0 came from the GitHub release tarball, because `elan`'s
  release lookup failed. Mathlib `v4.28.0` (`8f9d9cff6b`), the version the repository pins,
  was built from source, because the GHCR cache host is blocked.
- **Inputs.** All 30 inputs build: `Build completed successfully (2564 jobs)`.
- **v2 files.** Each was checked with `lake env lean conjectures-v2-opus-5-5/N.lean`. All 30
  compile with 0 errors and 135 `declaration uses sorry` warnings, one per theorem, and no
  other warnings.
- **One module built on demand.** 116 needed
  `Mathlib.MeasureTheory.Measure.Lebesgue.Complex`, which was built in a further 2489-job
  run.
- **Limits.** Compilation checks syntax and types only. The mathematical claims rest on the
  reviews' arguments. Spot checks were done numerically where feasible:
  - 94 (the ordered-quadruple count);
  - 97 (Danzer's 9-gon);
  - 112 (directed Ramsey brute force);
  - 115 (Chebyshev polynomials).

## Caveats

- **No independent comparison.** There are no Fable or Haiku reviews for 91–120, so nothing
  here was cross-checked by another model's review.
- **One session, in order.** The pipeline's ideal is a fresh process per problem
  (`GAME_PLAN.md` §5). These reviews ran in one session, interrupted by one worker restart
  that left the artifacts untouched. Bibliography reused across problems is attributed to
  its original log source.
- **DEFERRED references:**
  - 91: [Er97e]'s volume;
  - 92: [ErFi97] and [JJMT24];
  - 104: [Er83b];
  - 108: [Er79b];
  - 120: [Er83d], [Sv00] and [JLM24].
- **Label normalisation.** These were cleanup commits only, with no finding changed:
  - citation labels in 110, 111 and 113 (`ef8702ed`);
  - verdict labels in 114 and 118–120 (`a785cac5`);
  - two instances of first-person wording (`e0acd10d`);
  - one stale "not compiled yet" sentence in 91.
- **Site integration not done.** `palomar/build_manifest.py` (`CORPUS_DIRS`) and
  `site/stamp.py` read only the Fable and Haiku directories. Adding `opus-5-5-review/` and
  `conjectures-v2-opus-5-5/` would surface this batch in the explorer. That was out of scope.
