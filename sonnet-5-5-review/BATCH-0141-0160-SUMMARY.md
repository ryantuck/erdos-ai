---
batch: 0141-0160
reviewer_model: claude-sonnet-5-5
effort: max
review_date: 2026-10-06
selection: problems 141–160, the 20 problems that follow batch 0121–0140; the user answered "Yes: 141–160" to the proposed range
input_artifacts: conjectures/141.lean .. conjectures/160.lean
output_artifacts: conjectures-v2-sonnet-5-5/N.lean, sonnet-5-5-review/N.md (N = 141..160)
problems_reviewed: 20
verdict_accept: 0
verdict_accept_with_nits: 13
verdict_needs_revision: 7
confidence_high: 2
confidence_medium: 18
confidence_low: 0
source_recovered: 20
compile_status: pass
---

[AI - Claude Sonnet 5.5]: Sonnet 5.5 review batch 0141–0160

# Sonnet 5.5 review batch 0141–0160

This batch reviews problems 141–160 with the repository's pipeline (`FABLE_REVIEW.md` and
`FABLE_REVIEW_RUN.md`), run at **effort = max**. It follows the Sonnet 5.5 batch 0121–0140.

- **Order.** Problems were reviewed one at a time, in numerical order. Each was committed separately
  (subject `Sonnet 5.5 review N: …`) and pushed before the next one started.
- **Outputs.** The inputs in `conjectures/` are untouched. The fixed files are in
  `conjectures-v2-sonnet-5-5/`, and the reviews are in `sonnet-5-5-review/`. Each v2 file keeps the input's
  definitions and statements byte-identical except where a defect requires a change (142, 145, 146, 147, 148,
  150 and 160).
- **Independence.** No Fable, Haiku or Opus review exists for any of these 20 problems, so this batch has
  no cross-reviewer comparison. The only earlier reviews are the archived `deepmind/ai-review/N.md` files,
  which exist for 11 of the 20 and which Part E audits. The Opus review of Problem 113 treats the same
  results as 146 and 147, and the reviews of those two say so.
- **Compiled.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`) were built from source in the container.
  All 20 inputs and all 20 v2 files compile.

## Headline numbers

| Metric | Value |
|---|---|
| ACCEPT / ACCEPT WITH NITS / NEEDS REVISION | 0 / 13 / 7 |
| Confidence high / medium / low | 2 / 18 / 0 |
| Source page recovered | 20/20 (page captures in the session logs) |
| Status at capture → now | OPEN 15 → 13, PROVED 4 → 5, DISPROVED 1 → 2 (146 refuted and 152 proved after the capture) |
| Main statements **false as written** | 1: 147, false at the graph on no vertices (proved in Lean). It also asserts the direction that the page's banner records as disproved |
| Statements that **hold for a trivial reason** | 3: 142 (the main theorem; take $f=r_k$), 148 (the Konyagin lower bound, which follows from $F(k)\ge2$), 160 (the main theorem; a consequence of van der Waerden's theorem). 142 and 160 are proved in Lean in v2. For 148 Lean proves the implication from $F(k)\ge2$, and that fact is argued in the review and checked by search for $k\le7$ |
| Statements that miss the page's question | 142, 148 and 160, the three "estimate" problems. 148 also states a guess that the page does not make |
| Wrong polarity | 2: 146 (refuted after the capture), 147 (the page and the input's own docstring say DISPROVED) |
| Definition defects | 2: 145 (`sorry` inside `nextSquarefree`), 150 (an empty remainder counts as a separator; the main theorem is unaffected) |
| Inputs with a citation defect | 20/20 cite keys they never define (58 key citations in all). Every cited key is on the page, in the heading or in the remarks |
| Input declarations kept byte-identical in v2 | 13 of 20 problems (141, 143, 144, 149, 151–159). The main statement changes in 142, 146, 147, 148 and 160, where the input's statement is kept as a `first_pass*` variant or inside the negation (148 also repairs its Konyagin statement). One definition changes in 145 and in 150, with the theorem identical |
| Theorems: inputs → v2 | 23 → 275 (the extra 252 are page-recorded variants, reductions, helpers and Lean checks of the encoding) |
| v2 compile | 20/20 with 0 errors and no warning other than `declaration uses sorry` |
| `sorry` in v2 | 78 declarations contain one, and 3 more call one. The other 194 theorems are proved with `propext`, `Classical.choice` and `Quot.sound` only |

## Per-problem results

"Exact" means the main statement was judged a faithful encoding and kept byte-identical.

| # | Verdict | Conf. | Part A finding | Other findings |
|---|---|---|---|---|
| 141 | NITS | med | none; exact ($k$ consecutive primes in arithmetic progression, open, "yes" asserted) | 3 undefined keys; status and the infinitude question at $k=3$ missing; $k=3,\dots,6$ proved in Lean; [Er83] and [GrTa08] DEFERRED |
| 142 | **NEEDS REV** | med | trivially true: take $f=r_k$ (proved in Lean). v2 restricts $f$ to the closed-form class `IsExpLog`, an editorial choice | 3 undefined keys; the \$1000 offer of [Er97c] and the page's other variants missing; [GrTa17] and [LSS24] DEFERRED |
| 143 | NITS | med | none; exact (two sparseness questions; 143b proved by [KLL25]) | 6 undefined keys; \$500 prize and status missing; upstream records the $\liminf$ question as open, but it follows from [KLL25] (the model's own derivation, not formalized) |
| 144 | NITS | med | none; exact ($A(N)/N\to1$, PROVED by Maier–Tenenbaum) | 11 undefined keys; \$250 prize and the $c>1$ and $\beta$ variants missing; the name `Consecutive` is harmless (proved) |
| 145 | **NEEDS REV** | med | `nextSquarefree` contains a `sorry`, so `#print axioms` lists `sorryAx`; the theorem is exact | 3 undefined keys; the page's `[Ho73]`, `[GHH97]`, `[Ch23c]`, `[Gr98]` not cited; [Ch23c] and [Gr98] DEFERRED |
| 146 | **NEEDS REV** | med | asserts the conjecture that the mirror and upstream now record as refuted (a $2$-degenerate counterexample); v2 asserts the negation | 2 undefined keys; the refutation was not read (paper and Lean proof unavailable), so [OpenAI26] and the exact counterexample are DEFERRED |
| 147 | **NEEDS REV** | high | the page's banner is DISPROVED and the input's docstring agrees, yet the conjecture is asserted; the statement is also **false at the graph on no vertices** (proved in Lean) | 3 undefined keys; the prior review certified it and gave wrong titles for [Ja23] and [Ja23b] |
| 148 | **NEEDS REV** | med | the main theorem ($c_1^{2^k}\le F(k)\le c_2^{2^k}$) is a guess that the page does not make; the Konyagin lower bound is trivial (it follows from $F(k)\ge2$; the implication is proved in Lean) | 3 undefined keys; the constant $c_0$ of the page ($1.26408$) differs from upstream's ($1.5979$); [ElPl21] and [Ko14] DEFERRED |
| 149 | NITS | med | none; exact (the $\frac54\Delta^2$ conjecture, open) | 1 undefined key and 9 page keys uncited; sharpness at blow-ups of $C_5$ and $\chi'_s=\chi(L(G)^2)$ proved in Lean; the page's "at least" wording of [CGTT90] is false at $C_5$ |
| 150 | **NEEDS REV** | med | `IsVertexSeparator` counts the empty remainder as a separator (`Connected` against `Preconnected`), so $c(1)=c(2)=1$ and `numMinimalVertexCuts ⊤ = 1`; the limit is unaffected | 2 undefined keys; the page's second question ($c(3m+2)=3^m$) has the answer no already at $m=1$ (proved in Lean); the prior review found the defect and the input kept it |
| 151 | NITS | med | none; exact (the Erdős–Gallai $\tau(G)\le n-H(n)$, open) | 2 undefined keys; the page's "easy" $\tau\le n-\sqrt n$ fails at $n=2$ and $n=5$; checked over all graphs on at most 8 vertices |
| 152 | NITS | med | none; exact (isolated points of $A+A$ for Sidon sets) | 1 undefined key; proved after the capture (mirror, upstream), proofs unread |
| 153 | NITS | med | none; exact (mean squared gap of $A+A$ tends to $\infty$) | 1 undefined key; the remark on infinite Sidon sets unclear (DEFERRED) |
| 154 | NITS | med | none; exact ($A+A$ well distributed modulo $m$; PROVED (LEAN)) | 3 undefined keys; reduction to Lindström's theorem for $A$ proved in Lean; the prior review's title for [Ko99] is wrong |
| 155 | NITS | med | none; exact ($F(N+k)\le F(N)+1$ eventually) | 3 undefined keys; proved equal to the `maxSidon` form, equivalent to gaps between optimal Golomb ruler lengths tending to $\infty$; $k=1,2$ proved |
| 156 | NITS | med | none; exact (maximal Sidon set of size $O(N^{1/3})$) | 2 undefined keys; docstring calls it a "Conjecture", which the page does not; the page's "easy" bound $\lvert A\rvert\ge N^{1/3}/2$ proved for every maximal set |
| 157 | NITS | med | none; exact (infinite Sidon asymptotic basis of order 3; PROVED by Pilatte) | 3 undefined keys; the prior review's [Er94b] and [Pi23] are wrong or unsupported |
| 158 | NITS | med | none; exact ($\liminf=0$ for sets with at most 2 representations); the real `liminf` is genuine (counting bound $k^2\le8N+4$, in Lean) | 1 undefined key; hypotheses proved satisfiable; the page's Sidon case added |
| 159 | NITS | med | none; exact ($R(C_4,K_n)\ll n^{2-c}$, open) | 4 undefined keys; encoding proved equal to Mathlib's and upstream's; the prior review's $R(C_4,K_1)=0$ is wrong (it is $1$); the page gained a \$100 prize after the capture |
| 160 | **NEEDS REV** | high | the main theorem ($h(N)\to\infty$) is not the page's request (estimate $h(N)$) and is true by van der Waerden (proved in Lean from Hales–Jewett) | 1 undefined key; a one-line `:= sorry` (Part D); Hunter's bound and the lower bound of [BlSi23] and [KeMe23] added as variants |

NITS is short for ACCEPT WITH NITS. Every v2 file also adds a module docstring, page-recorded variants,
reductions between them, or Lean proofs of what the review argues. Each variant is labelled PROVED, OPEN or
DISPROVED with its source.

## Defect classes

| Class | Count | Problems |
|---|---|---|
| undefined-citation-key | 20 | 141–160 |
| trivially-true-statement | 3 | 142, 148, 160 |
| wrong-polarity | 2 | 146, 147 |
| wrong-target-statement | 2 | 148, 160 |
| false-at-small-parameters | 1 | 147 |
| sorry-in-definition | 1 | 145 |
| empty-remainder-separator | 1 | 150 |

`undefined-citation-key` means keys are cited but never defined, as in the Opus batch and in batch 0121–0140.
No input here cites nothing at all, and none cites a key the page does not have.

Five patterns stand out:

- **The "estimate" problems (142, 148, 160).** The page asks for an asymptotic formula (142) or for good estimates
  (148, 160). The inputs state an existential with no closed-form requirement, whose witness is $r_k$ itself
  (142); a guess of the first pass, with a Konyagin half that follows from $F(k)\ge2$ (148); and
  $h(N)\to\infty$, a consequence of van der Waerden's theorem (160). In each case v2 proves the triviality in
  Lean and states the page's request as "the order of magnitude is a closed form", with one shared class
  `IsExpLog` (from `142.lean`). **That class is an editorial choice.** The page does not say which closed forms
  count, and the first pass's statement is kept as a labelled variant.
- **Direction (146, 147).** 146 asserts a conjecture that was refuted after the capture. 147 asserts one that the
  page's banner and the input's own docstring call DISPROVED, which is the same self-contradiction as in Problems
  105, 110 and 113 of the Opus batch. 147 is moreover false at the empty graph, so a formal refutation of the
  input would say nothing about Janzer's theorems. v2 adds `[Nonempty U]`, as upstream does.
- **Lean junk values and Mathlib conventions (145, 150, 158, 159).** A `sorry` inside a definition gives every
  consequence `sorryAx` (145). Mathlib's `Connected` requires a nonempty vertex type, so an empty remainder is
  "disconnected" and the whole vertex set counts as a separator (150). A `liminf` of a real sequence is a junk
  value unless the sequence is bounded, and `Set.ncard` is `0` on an infinite set; both are proved harmless in 158.
  The value $R(C_4,K_1)$ is $1$, not $0$ (159). v2 fixes the first two and proves the others harmless.
- **The Sidon cluster (152–158).** Seven consecutive problems share their conventions (Sidon sets, the sumset,
  `range N` against $\{1,\dots,N\}$) and one key, [ESS94], whose entry is in the site's `/latex/156`
  bibliography. The reviews check the shared definitions against Mathlib and upstream, compute small cases
  exhaustively, and prove the translations in Lean. 155 is shown equivalent to the gaps between consecutive
  optimal Golomb ruler lengths tending to infinity, and 156's easy lower bound is proved for every maximal Sidon
  set.
- **Accepted statements validated in Lean (141, 143, 144, 149, 151–159).** In the 13 accepted problems the defects
  are chiefly the citations and the missing status. v2 adds Lean proofs that the encoding accepts genuine instances
  and rejects wrong ones: $k=3,\dots,6$ in 141, $A(30)=8$ in 144, sharpness at $C_5$ in 149, the exact translation
  to $F(N+k)\le F(N)+1$ in 155, the counting bound in 158, and the equality with Mathlib's definitions in 152, 154
  and 159.

## Status changes after capture

Captures date from 2026-02-20 to 2026-03-05. The mirror snapshot is `b916d95` (2026-09-28), and upstream
`formal-conjectures` is at `df3f12d` (2026-10-01).

| # | At capture | Now | Effect on the input |
|---|---|---|---|
| 146 | OPEN, prize \$500 | `disproved (Lean)` (mirror, `7b7132c`, 2026-08-31; Lean refutation recorded in `be86208`, 2026-08-02); upstream `answer(False)` with a counterexample variant | the asserted direction is now refuted: polarity defect; v2 asserts the negation |
| 152 | OPEN | informal `proved` (2026-04-03), formal `proved (Lean)` (2026-08-23); upstream `solved`, proofs credited to [DM26a] and [DM26b] | the "true" direction that the input asserts is the proved one; label updated |
| 159 | OPEN | still open; the page was edited between 2026-03-03 and 2026-03-10 (a \$100 prize and the reference [Er78, p. 34]) | the prize and the reference are missing from the input; the statement is unaffected |
| 144, 150 | PROVED | the mirror adds `proved (Lean)` (2026-08-24 and 2026-03-31) | no effect |
| 147 | DISPROVED | `disproved (Lean)` since 2026-08-24 | no effect; the polarity defect was present at capture |
| 143, 160 | OPEN | open; upstream's variants are stale or weaker (143: the $\liminf$ question follows from [KLL25]; 160: `better_upper` is already implied by Hunter's bound, and its exponent $1/12$ is the weaker one) | no effect on the inputs |

The other 12 problems are unchanged in status since the capture. The proofs behind 146 and 152, and the Lean proofs
that the mirror records for 144, 147 and 150, could not be read in this container. v2 records them with provenance
and labels them unverified. Only 146 depends on one for its verdict, and that is why its confidence is medium.

## Prior-review audit (`deepmind/ai-review/`)

11 of the 20 problems have an archived prior review: 144, 146, 147, 148, 149, 150, 151, 154, 156, 157 and 159.
141, 142, 143, 145, 152, 153, 155, 158 and 160 have none. Every prior review was written against a styled copy
in `deepmind/deepmind/` (sometimes an earlier state of it), never against the raw `conjectures/` file reviewed
here. The styled copies need upstream's imports and were not compiled here.

**Right on the core defect, but not applied to the raw corpus.**

- 150: the prior review found that an empty remainder counts as a separator (`numMinimalVertexCuts K₃ = 1`
  instead of $0$) and judged it harmless for the limit, which is right. The styled copy has the fix, and the raw
  input kept the defect.
- 146, 147, 154, 156, 157, 159: the suggestions to reuse Mathlib's `extremalNumber`, `IsContained` and
  `cycleGraph 4` and upstream's `IsSidon` and `Set.IsAsymptoticAdditiveBasisOfOrder` were implemented in the styled
  copies and never in the raw files. v2 proves the equivalences with Mathlib's definitions for 146, 147, 154 and 159.
- References, variants and refactors added to styled copies (144, 149, 150, 154, 156, 159) likewise never reached
  the raw files. That is why all 20 raw files have citation defects.

**Missed the defect.**

- 147 was certified as having "no mathematical errors" with `answer(False)` encoding the disproof, while the
  statement is false at the graph on no vertices, so a formal disproof would be trivial.
- 148 was called "mathematically correct and complete" while the Konyagin statement is trivially true and the main
  theorem is a guess. The review noticed that the guess is the formalization authors' own and accepted it.
- 150's styled copy marks $c(3m+2)=3^m$ as open, and it is false at $m=1$.
- 159 gave $R(C_4,K_1)=0$ (the value is $1$), and 156 found "no mathematical flaws" and missed that the docstring's
  "conjecture that the answer is YES" is not on the page, which calls the problem a question.
- 151 reversed the implication with Problem 610, and left the page's "easy" bound $\tau\le n-\sqrt n$ unchecked
  (it fails at $n=2$ and $n=5$).

**Wrong or invented bibliographic data**, some of it written into styled copies:

- 147 gave titles for `[Ja23]` and `[Ja23b]` that contradict the page's bibliography.
- 148 gave titles for `[Ko14]` and `[ElPl21]` that conflict with upstream's; no `/latex/148` fetch exists to settle
  which paper the page cites.
- 149 certified a key coined by the session that wrote the styled copy, `[ErNe85]` ("proposed at a seminar in
  Prague"). The page's key is `[Er88]`, and no capture contains the coined key.
- 150 gave `[Er88]` and `[Br24]` titles that the site's bibliography (`/latex/934`, `/latex/77`, `/latex/150`)
  contradicts, and concluded "no issues found"; 151 gave `[Er88]` a different wrong title.
- 154 gave `[Ko99]` the title of a different paper; the styled copy has it right.
- 156 accepted "the website does not provide a full citation", while `/latex/156` has both full entries.
- 157 gave `[Er94b]` the title of a different paper and `[Pi23]` a title that no fetch supports, and repeated both
  in the styled copy.
- 159's styled copy gave `[Er84d]` a title that `/latex/772` contradicts, and the review accepted `[Er81]`'s title
  as "shorthand".
- 146's styled copy gives `[Er91]` and `[Er97c]` titles that no recovered bibliography supports.

**Stale or irreproducible reuse claims.** Several line citations into the pinned upstream clone are stale: the
`IsSidon` definition is at line 67, not 38 (154, 157), and the library lines cited in 156 as 38, 104 and 127 are 67,
133 and 156. The checklist reviews of 156, 157 and 159 cite lines that match neither the input nor the styled copy
(they describe an earlier version), and the checklist of 149 cites stale lines of its styled copy. Where the claim
matters, the review states what the present clone has.

**Mathematical slips.**

- 146: "the set of edge counts is non-empty and bounded" (false for an edgeless $H$); "Mathlib's `extremalNumber`
  avoids the empty-set subtlety of `sSup`" (both conventions give $0$); the $r=1$ bound attributed to Erdős–Gallai
  (it is the Erdős–Sós form).
- 147: "the set of edge counts is non-empty" (false in the same degenerate case).
- 149: the odd-$\Delta$ refinement (the arithmetic is right, but it is not on the page and its source is
  DEFERRED) and "known for $\Delta\le3$" (unsupported).
- 154: "uses Lean's anonymous constructor syntax for `r < m`" (it is binder-predicate notation).

The prior reviews' encoding checks were usually right: the finiteness behind `Set.ncard` and `sSup`, the guards,
and the equivalence of a custom definition with Mathlib's.

## Compile verification

- **Toolchain.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), the version the repository pins, built from
  source in the container.
- **Inputs.** All 20 build with 0 errors and 24 `declaration uses sorry` warnings: the 23 input theorems and the
  definition `nextSquarefree` of 145.
- **v2 files.** Each was checked with `lake env lean conjectures-v2-sonnet-5-5/N.lean`. All 20 compile with 0
  errors and 78 `declaration uses sorry` warnings, and no other warnings.
- **Axiom audit.** `#print axioms` was run for all 275 theorems in the v2 files. None depends on an axiom
  other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. No v2 file declares an `axiom`, and
  none uses `native_decide`. The explicit finite checks use `decide +kernel` (142, 145, 146, 155, 156).
- **Static checks (Part D).** No v2 file has a `sorry` inside a definition, a one-line `:= sorry`, or a debug
  command, and all 341 declarations in the v2 files have a docstring. Among the inputs, 145 has a `sorry` inside
  `nextSquarefree` (fixed in v2) and 160 has a one-line `:= sorry` (line 37; a style item, since v2 replaces the
  statement). No input declares an `axiom`.
- **Limits.** Compilation checks syntax, types and the proofs. The cited literature results are stated as the
  pages word them and were not checked against the papers. Spot checks were done by exhaustive or
  numerical computation (programs in the session scratchpad, none part of the repository):
  - 141: the first runs of $k$ consecutive primes in arithmetic progression for $k=3,\dots,6$, by a sieve to $3\cdot10^8$;
  - 142: $r_k(N)$ for $k=3,\dots,6$ and $N\le36$;
  - 144: $A(N)$ up to $10^7$;
  - 145: the moments $\frac1N\sum(\mathrm{next}(s)-s)^\alpha$ for $\alpha=0,\dots,4$ up to $10^9$;
  - 148: $F(k)$ for $k\le7$ ($1,0,1,6,72,2320,245765$) and the constants of the page;
  - 149: $\chi'_s$ over all labelled graphs on at most 7 vertices, and for cycles, complete graphs and blow-ups of $C_5$;
  - 150: $c(n)$ for $n\le7$ ($1,2,5,9,14$ for $n=3,\dots,7$) and the graphs of independent paths;
  - 151: $\tau$ and $H(n)$ over all labelled graphs on at most 8 vertices ($2^{28}$ for $n=8$);
  - 152: the least number of isolated points of $A+A$ for Sidon sets of size 1 to 8;
  - 153: the least mean squared gap of $A+A$ for Sidon sets of size 2 to 8;
  - 155: the optimal Golomb ruler lengths for 2 to 12 marks;
  - 156: the least size of a maximal Sidon set in $\{0,\dots,N-1\}$ for $N\le78$;
  - 159: $R(C_4,K_n)=4,7,10$ for $n=2,3,4$, and $R(C_4,K_5)\ge14$;
  - 160: $h(N)$ for $N\le50$.

  Problems 143, 146, 147, 154, 157 and 158 needed no computation beyond their Lean proofs.

## Caveats

- **No independent comparison.** There are no Fable, Haiku or Opus reviews for 141–160, so nothing here was
  cross-checked by another model's review.
- **One session, in order.** The pipeline's ideal is a fresh process per problem (`GAME_PLAN.md` §5). These
  reviews ran in one session. The session's context was summarized and resumed at least once, after Problem 160
  and during the end-of-batch work, and the worker process was restarted several times. All 20 inputs and all 20
  v2 files were recompiled after the last resumption. Bibliography reused across problems is attributed to its
  original log source, and the [ESS94] entry of 152, 153, 155, 157 and 158 rests on the one fetch of `/latex/156`.
- **DEFERRED items** (each caps that problem's confidence at medium, except in 147 and 160, where the verdict
  rests on a defect proved in Lean and the unread sources are listed at the end):
  - 141: [Er83] and [GrTa08];
  - 142: [GrTa17] and the title of [LSS24];
  - 143: [Er92c] and [KLL25], and the venue of [ESS67];
  - 144: [Er79e] and [Er85e], and the venue of [Er82e];
  - 145: [Ch23c] and [Gr98], and the endpoint $11/3$ of the Greaves–Harman–Huxley result;
  - 146: the exact form of the counterexample and the title and venue of [OpenAI26];
  - 148: which paper `[ElPl21]` is, the constant it states, and the explicit form of [Ko14];
  - 149: eight cited keys and Mahdian's thesis, the reading of "$C_4$-free" and "$C_5$-free", the source of the
    odd-$\Delta$ refinement and of the case $\Delta\le3$;
  - 150: the later developments that upstream records, and whether [Er88] means the same notion of minimal cut;
  - 151: the exact form of the "easy bound" in [EGT92], the results of [EGT92] and [AKS80] that the page of [610]
    records, and the bibliography of [AKS80];
  - 152: the later proofs [DM26a] and [DM26b] and the new text of the page;
  - 153: the meaning of the remark on infinite Sidon sets;
  - 154: Lindström's theorem and Kolountzakis's strengthening, and the Lean proofs that upstream links;
  - 155: the meaning of the remark on $k\approx\epsilon N^{1/2}$;
  - 156: the two cited papers, the page of Problem 340 and OEIS A382397;
  - 157: Pilatte's paper and proof, and the title and venue of [Pi23];
  - 158: the source of Erdős's result in the Sidon case;
  - 159: the cited papers, and the page's current heading and bibliography after its edit;
  - 147 and 160 (confidence high): [Ja23] and [Ja23b] were not read (147), and [Er89], the MathOverflow items and
    the sources of the page's bounds were not seen (160). Neither bears on the defects proved in Lean;
  - no `/latex/N` fetch exists for 141, 142, 143, 145, 148, 149, 152, 153, 155, 157, 158 and 160, so those pages' own
    bibliographies were not seen. Their entries come from other problems' fetches or from upstream's docstrings, or
    are DEFERRED as listed above. 144, 146, 147, 150, 151, 154, 156 and 159 have their own fetch.
- **Post-capture results unchecked.** The Lean proofs and papers behind the status changes above (146, 152, and the
  Lean statuses of 144, 147 and 150) were not read.
- **Log line numbers.** The Addenda cite session-log records with 1-based line numbers (the first record of a log is
  line 1). Reviews 141 and 142 were first written with 0-based numbers and were corrected in `2cad1230`. The same
  correction for batch 0121–0140 is on that batch's branch (`7b6cf8f7`). In the Opus batch (`opus-5-5-review/`),
  163 log-line numbers in reviews 91–120 were 0-based (all of them in 91–112, and all but the `Write` and `Edit`
  lines in 113–120; reviews 1101–1110 are 1-based). This batch does not change them. PR #30 renumbers them.
- **Label normalisation.** These were cleanup commits only, with no finding changed:
  - the provenance of `[ESS94]` recorded for 152 and 153 (`41bca10b`);
  - "defines it" corrected to "defines nothing" in the verdict blocks of 149, 152, 153, 158 and 160, and the Part D
    row of 160 corrected to show its one-line `:= sorry` (this commit).
- **Quoted first-person text.** The v2 files and reviews contain first-person words only inside verbatim quotes
  of a page remark or of a paper title (for example "Some of my favorite problems and results", "Some of my
  forgotten problems…", "On the combinatorial problems which I would most like to see solved"), as the Roman
  numeral or an initial "I" ("On sum sets of Sidon sets, I", "Todinca, I."), or inside quotations of the input's own
  docstrings that a review flags (for example "we have" in the docstring of `ErdosSeparated` in 143).
- **Site integration not done.** `palomar/build_manifest.py` (`CORPUS_DIRS`) and `site/stamp.py` read only the
  Fable and Haiku directories. Adding `sonnet-5-5-review/` and `conjectures-v2-sonnet-5-5/` (and
  `opus-5-5-review/`) would surface these batches in the explorer. That was out of scope.
