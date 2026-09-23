---
batch: 1101-1110
reviewer_model: claude-opus-5-5
effort: max
review_date: 2026-09-23
selection: the ten lowest-numbered problems reviewed in both fable-review/ and haiku-review/
input_artifacts: conjectures/1101.lean .. conjectures/1110.lean
output_artifacts: conjectures-v2-opus-5-5/N.lean, opus-5-5-review/N.md (N = 1101..1110)
problems_reviewed: 10
verdict_accept: 0
verdict_accept_with_nits: 6
verdict_needs_revision: 4
confidence_high: 1
confidence_medium: 9
confidence_low: 0
source_recovered: 10
compile_status: pending
---

[AI-Generated]: Opus 5.5 review batch 1101–1110

# Opus 5.5 review batch 1101–1110

This batch is a third, independent review of ten problems that were already reviewed by
Fable 5 (`fable-review/`) and by Haiku 4.5 (`haiku-review/`). It followed the same
pipeline, `FABLE_REVIEW.md` and `FABLE_REVIEW_RUN.md`, run at **effort = max**.

- **Order.** Problems were reviewed one at a time, never in parallel. Each problem was
  committed separately (subject `Opus 5.5 review N: …`) before the next one started.
- **Selection.** Problems 1101–1179 are the overlap between the two earlier review sets.
  This batch takes the ten lowest-numbered of them, a content-blind rule, so no problem
  was chosen for how the earlier reviewers had graded it.
- **Independence.** No `fable-review/N.md`, `haiku-review/N.md`, `conjectures-v2/N.lean`
  or `conjectures-v2-haiku/N.lean` for these ten problems was read until all ten reviews
  were committed. The comparison below was written afterwards. One incidental exposure
  happened while surveying the repository: a single grep line from
  `conjectures-v2/1101.lean`. It is disclosed in `opus-5-5-review/1101.md`.
- **Outputs.** The inputs in `conjectures/` are untouched. Fixed files are in
  `conjectures-v2-opus-5-5/`, mirroring `conjectures-v2-haiku/`. Nothing is
  compile-verified, because this container has no Lean toolchain.

## Headline numbers

| Metric | Opus 5.5 | Fable 5 | Haiku 4.5 |
|---|---|---|---|
| ACCEPT | 0 | 0 | 3 |
| ACCEPT WITH NITS | 6 | 7 | 4 |
| NEEDS REVISION | 4 | 3 | 3 |
| Source page recovered | 10/10 | 10/10 | 4/10 (+1 partial) |
| Statements found **false as written** | 2 (1102, 1105) | 2 (1102, 1105) | 0 |

## Per-problem comparison

| # | Opus 5.5 | Fable 5 | Haiku 4.5 | What Opus found |
|---|---|---|---|---|
| 1101 | NITS | NITS | NEEDS REV (answer-form) | `maxGap` drops the gap that straddles $x$. Proven harmless and aligned with the source. `[Er81h]` undefined. |
| 1102 | **NEEDS REV** | **NEEDS REV** | ACCEPT | Part 2 required $a(j)\le f(j)j$ for **every** $j$, which is false: $f=\log(j+1)$ forces $a(1)=0$. Made eventual. |
| 1103 | **NEEDS REV** | NITS | NITS | Main statement *eventually* super-polynomial is strictly stronger than Erdős's "no polynomial growth". Switched to the literal (frequent) form; the old form kept as a variant. |
| 1104 | **NEEDS REV** | NITS | ACCEPT | The theorem is the *known* Θ-order, presented as the open problem. Relabelled as solved; sharp bounds added. |
| 1105 | **NEEDS REV** | **NEEDS REV** | NITS | `antiRamseyNumber` counts colours on the diagonal of `Sym2`, so it equals $\mathrm{AR}+n$ and both theorems are false (brute force: 7 vs 3 at $(4,C_3)$). |
| 1106 | NITS | NITS | NITS | Exact. $F(n)>n$ for $116\le n\le700$ by computation. |
| 1107 | NITS | NITS | NITS | Exact. The $r=2$ exceptions reproduce $\{7,15,23,87,111,119\}$. |
| 1108 | NITS | NITS | ACCEPT | Exact. The 0!/1! convention follows the page's own $0\in\mathbb N$ (the Mahler example uses $7^0$). |
| 1109 | NITS | NEEDS REV | NEEDS REV (answer-form) | The weaker $N^{o(1)}$ sub-question was missing and has been added. Graded B2, so it does not cap the verdict. |
| 1110 | NITS | NITS | NEEDS REV (answer-form) | Exact. Pins the open cases to $(p,q)\in\{(5,3),(5,2),(9,2)\}$. |

Every one of the ten files cited at least one reference key without defining it
(`undefined-citation-key`). All are fixed in v2 with provenance-noted data.

## Where the three reviewers agree and differ

**The two false statements (1102, 1105).** Opus and Fable independently found both and
proposed the same fixes: the eventual bound for 1102, and counting only edge colours for
1105. Haiku accepted both files.

For 1105, Haiku's review checks `HasRainbowCopy` and the graphs in detail. It then states
that the colour count is bounded by $|E(K_n)|=n(n-1)/2$, which is exactly the claim the
diagonal of `Sym2` breaks: the true bound is $n(n+1)/2$. That is the kind of semantic slip
no static check or compiler catches, and indeed the input compiled.

**Same facts, different grades (1103, 1104, 1109).**

- **1103.** Fable identified the eventual-versus-literal gap but graded it an
  interpretation "nuance". It kept the eventual form as the main statement and added the
  literal one as a variant. Opus grades it a Part A defect and makes the literal form
  primary, because the literal form is the only proposition the page attributes to Erdős
  and the two are not decision-equivalent. Haiku endorsed the eventual form as "exactly"
  Erdős's expectation, repeating the prior `deepmind/ai-review` error.
- **1104.** Fable documented the solved-Θ status as polish. Opus treats "open problem
  encoded as a known theorem" as a status defect (A5). A reader of the corpus would take a
  proof of `erdos_problem_1104` as settling #1104, and it would not. The upstream file,
  captured in the logs, likewise formalizes only the solved bounds and leaves the main
  statement as a TODO.
- **1109.** All three noticed the weaker sub-question in some form. Fable gave NEEDS
  REVISION, graded as a B2 missing part. Opus gave ACCEPT WITH NITS, because
  `FABLE_REVIEW.md` caps the verdict only for Part A defects, and Fable itself graded the
  identical defect class that way for problem 1142. Haiku's NEEDS REVISION was for the
  `answer()` form, and it treated the sub-question as optional enrichment.

**Haiku's other NEEDS REVISION verdicts (1101, 1109, 1110)** were all for writing yes/no
questions as direct assertions instead of `answer(sorry) ↔ …`. This raw corpus has no
`answer()` elaborator, and direct assertion of the asked direction is its convention.
Opus and Fable both treat that as acceptable.

**Scholarship.** Opus recovered original-pipeline `/latex` extractions for keys shared with
sibling problems:

- `/latex/18` for `[Er81h]`;
- `/latex/1103` for `[vDTa25]`;
- `/latex/1011`, `/latex/627`, `/latex/610` and `/latex/165` for the 1104 keys;
- `/latex/854` for `[Ob1]`;
- `/latex/941` for `[He88]`;
- `/latex/1109` and `/latex/1110`.

One concrete payoff is in 1104. Fable's `conjectures-v2/1104.lean` carries the
model-written gloss "Hefty, **L.**, Horn, P., King, **R.**", with the wrong initials; the
`/latex` extraction gives Z., P., D., F. Fable's reviews did catch the other two
hallucinated glosses that recur across this batch: "Sumsets of squarefree numbers" for
`[vDTa25]` and "Some applications of graph theory…" for `[Er81h]`.

## Caveats

- **No compiler.** Every v2 change is uncompiled. Main-theorem statements were left
  byte-identical except in the three places where a Part A fix required a change:
  - 1102: the Part 2 quantifier;
  - 1103: the main conclusion;
  - 1105: the `antiRamseyNumber` counting set.

  1101's `maxGap` window was also aligned, which is proven not to change either theorem.
- **One session, run in order.** The pipeline's ideal is a fresh process per problem
  (`GAME_PLAN.md` §5). These ten reviews ran in one session, in order, so later reviews
  could reuse bibliography found in earlier ones: `[Er81h]` in 1102–1103 and `[Ob1]` in
  1107–1108. Each reuse is attributed to its original log source, not to the earlier
  review.
- **Site integration not done.** `palomar/build_manifest.py` and `site/stamp.py` read only
  `fable-review/` and `haiku-review/`. Adding `opus-5-5-review/` and
  `conjectures-v2-opus-5-5/` to their lists would surface this batch in the explorer.
  That was out of scope for this change.
