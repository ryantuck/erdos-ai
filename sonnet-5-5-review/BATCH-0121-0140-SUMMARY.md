---
batch: 0121-0140
reviewer_model: claude-sonnet-5-5
effort: max
review_date: 2026-10-05
selection: problems 121–140, the 20 problems that follow the earlier Opus batch; the user asked for 20 problems and named no range
input_artifacts: conjectures/121.lean .. conjectures/140.lean
output_artifacts: conjectures-v2-sonnet-5-5/N.lean, sonnet-5-5-review/N.md (N = 121..140)
problems_reviewed: 20
verdict_accept: 0
verdict_accept_with_nits: 9
verdict_needs_revision: 11
confidence_high: 10
confidence_medium: 10
confidence_low: 0
source_recovered: 20
compile_status: pass
---

[AI - Claude Sonnet 5.5]: Sonnet 5.5 review batch 0121–0140

# Sonnet 5.5 review batch 0121–0140

This batch reviews problems 121–140 with the repository's pipeline (`FABLE_REVIEW.md` and
`FABLE_REVIEW_RUN.md`), run at **effort = max**. It follows the Opus 5.5 batch 0091–0120.

- **Order.** Problems were reviewed one at a time, in numerical order. Each was committed separately
  (subject `Sonnet 5.5 review N: …`) and pushed before the next one started.
- **Outputs.** The inputs in `conjectures/` are untouched. The fixed files are in
  `conjectures-v2-sonnet-5-5/`, and the reviews are in `sonnet-5-5-review/`. Each v2 file keeps the input's
  definitions and statements byte-identical except where a defect requires a change.
- **Independence.** No Fable, Haiku or Opus review exists for any of these 20 problems, so this batch has
  no cross-reviewer comparison. The only earlier reviews are the archived `deepmind/ai-review/N.md` files,
  which exist for 12 of the 20 and which Part E audits.
- **Compiled.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`) were built from source in the container.
  All 20 inputs and all 20 v2 files compile.

## Headline numbers

| Metric | Value |
|---|---|
| ACCEPT / ACCEPT WITH NITS / NEEDS REVISION | 0 / 9 / 11 |
| Confidence high / medium / low | 10 / 10 / 0 |
| Source page recovered | 20/20 (page captures in the session logs) |
| Main statements **false as written** | 7: 122, 123, 129, 132, 133, 135, 136. Six are refuted in Lean in v2. 129 is refuted by the page's own remark, and v2 proves in Lean that the remark implies the refutation |
| Statements that miss the page's question, label or status | 131 (states a guess, not the question), 124 (a proved part labelled OPEN), 125 (refuted after the capture), 138 (the definition rests on an `axiom`) |
| Wrong polarity | 3: 125, 129, 135 |
| Inputs with a citation defect | 20/20 cite keys they never define. Two cite a key the page does not have: `[ErPa90]` in 133 and `[Al94]` in 134 |
| Theorems: inputs → v2 | 29 → 153 (the extra 124 are page-recorded variants, reductions and helpers) |
| v2 compile | 20/20 with 0 errors and no warning other than `declaration uses sorry` |
| `sorry` in v2 | 84 declarations contain one, and 4 more call one. The other 65 theorems are proved with `propext`, `Classical.choice` and `Quot.sound` only |

## Per-problem results

"Exact" means the main statement was judged a faithful encoding and kept byte-identical.

| # | Verdict | Conf. | Part A finding | Other findings |
|---|---|---|---|---|
| 121 | NITS | high | none; exact (Tao: $F_k(N)\le(1-c+o(1))N$ for $k\ge4$, the page's resolution) | 7 undefined keys; the literal negations of the page's questions and the $F_2,F_3,F_4$ results missing |
| 122 | **NEEDS REV** | med | `HasErdos122Property` is unsatisfiable for every $f$, so the main theorem is false (proved in Lean); the page's wording has the same gap | 3 undefined keys; the intended statement DEFERRED |
| 123 | **NEEDS REV** | high | false at the degenerate triples that `1 ≤ a,b,c` admits ($a=b=c=1$, and $a=1$ in general); v2 uses `2 ≤` | proved after capture (mirror, upstream); 4 undefined keys |
| 124 | **NEEDS REV** | med | Part 1 is labelled OPEN although the page's remarks record its proof; both statements are exact | 3 undefined keys; [Me04] DEFERRED |
| 125 | **NEEDS REV** | med | asserts positive lower density, which the mirror and upstream now record as refuted | undefined keys; [Me01] and [HaMe24] DEFERRED |
| 126 | NITS | high | none; exact ($f(n)/\log n\to\infty$) | 4 undefined keys; now recorded as proved |
| 127 | NITS | high | none; exact (largest bipartite subgraph above the Edwards bound) | false remark "$f(\binom n2)=0$ from $K_n$" (odd $n$ only); 2 undefined keys, the page's own key absent |
| 128 | NITS | med | none; exact (Erdős–Rousseau triangle question, open) | undefined keys; 5 references DEFERRED; the page's partial results missing |
| 129 | **NEEDS REV** | high | asserts $R(n;3,r)<C^{\sqrt n}$, which the page's own remark refutes ($R(n;3,2)\ge C^n$): wrong polarity | `[Er97b]` undefined; `sInf ∅` junk at $r=1$ |
| 130 | NITS | high | none; exact (infinite chromatic number of an integer-distance graph) | false remark "the clique number is always finite"; 2 undefined keys; now recorded as proved |
| 131 | **NEEDS REV** | high | the main theorem states the first pass's guess ($F(N)\ge N^{1/4-\varepsilon}$), not the page's question | 5 undefined keys |
| 132 | **NEEDS REV** | high | ordered pairs counted against $n$ make Part 1 false (a square with its centre; proved in Lean) | undefined keys; \$100 prize missing |
| 133 | **NEEDS REV** | med | `sInf` of a downward-closed set makes $f\equiv0$ (proved in Lean), so the Moore bound and Alon's conjecture are false | spurious key `[ErPa90]`; Alon's note DEFERRED |
| 134 | NITS | med | none; exact (a triangle-free graph made diameter 2 with $\delta n^2$ edges) | invented key `[Al94]` dropped; Alon's note DEFERRED |
| 135 | **NEEDS REV** | high | asserts the refuted "yes" (Tao), and is false at a single point (no size guard) | undefined keys; \$250 prize missing |
| 136 | **NEEDS REV** | med | ordered colourings give each edge two colours: $f(9)\le5$ and $f(n)=O(\sqrt n)$ (proved in Lean), so all three theorems are false | undefined keys; one attribution DEFERRED |
| 137 | NITS | med | none; exact (Erdős–Selfridge, the negation of the question as asked) | undefined keys; no `/latex/137` fetch |
| 138 | **NEEDS REV** | med | `W` is defined from `axiom vanDerWaerden`; v2 proves it from Mathlib | 11 undefined keys; 2 DEFERRED |
| 139 | NITS | med | none; exact (Szemerédi, $r_k(N)=o(N)$) | `[Sz75]` undefined; 4 references DEFERRED |
| 140 | NITS | high | none; exact ($r_3(N)\ll N/(\log N)^C$, the Kelley–Meka consequence) | undefined keys; `p.11` dropped |

NITS is short for ACCEPT WITH NITS. Every v2 file also adds page-recorded variants, reductions between
them, or Lean proofs of what the review argues. Each variant is labelled PROVED, OPEN or DISPROVED with its
source.

## Defect classes

| Class | Count | Problems |
|---|---|---|
| undefined-citation-key | 20 | 121–140 |
| wrong-polarity | 3 | 125, 129, 135 |
| false-at-small-parameters | 2 | 123, 135 |
| misleading-docstring-remark | 2 | 127, 130 |
| trivially-false-statement | 1 | 122 |
| known-result-as-open-problem | 1 | 124 |
| wrong-target-statement | 1 | 131 |
| ordered-pair-threshold | 1 | 132 |
| wrong-extremal-operator | 1 | 133 |
| wrong-citation-key | 1 | 134 |
| wrong-definition-asymmetric-colouring | 1 | 136 |
| axiom-in-definition | 1 | 138 |

`undefined-citation-key` means keys are cited but never defined, as in the Opus batch. No input here cites
nothing at all.

Four patterns stand out:

- **Statements false as written (122, 123, 129, 132, 133, 135, 136).** In six of the seven the falsity is a
  small elementary fact, and v2 proves it in Lean: an unsatisfiable property (122), degenerate triples
  (123), a square with its centre (132), `sInf` of a downward-closed set (133), a single point (135), and a
  5-colouring of $K_9$ (136).
- **Ordered pairs (129, 132, 136).** The same encoding of an edge by an ordered pair is harmless in 129,
  where a monochromatic clique needs every ordered pair to agree, and decisive in 132 and 136, where
  a threshold or a count of distinct values reads each edge twice. In 136 it makes all three theorems false,
  and the prior review found the mechanism and left it as "potentially".
- **Direction and target (125, 129, 131, 135).** Three inputs assert a direction that is refuted (129 by the
  page's own remark, 135 by Tao, 125 by a result after the capture), and one asserts a conjecture the page
  does not make (131). 137 asserts the negation of the question as asked, which is the conjectured answer
  and is documented, so it passes.
- **Trust base (138).** The only `axiom` in the 20 inputs makes a true theorem (van der Waerden) a
  dependency of the main statement. Mathlib has the infinite form, and v2 proves the finite form by
  compactness. Compare `fable-review/1137.md`, where an axiom did not determine a definition at all.

## Status changes after capture

Captures date from 2026-02-20 to 2026-03-05. The mirror snapshot is `b916d95` (2026-09-28), and upstream
`formal-conjectures` is at `df3f12d` (2026-10-01).

| # | At capture | Now | Effect on the input |
|---|---|---|---|
| 123 | OPEN | `proved (Lean)` from `8cbad71` (2026-07-17); upstream `answer(True)` | the "yes" direction is the proved one; label updated |
| 125 | OPEN | `disproved (Lean)` (mirror 2026-03-30); upstream `positive_lower_density : answer(False)` | the asserted direction is now refuted: polarity defect |
| 126 | OPEN | `proved` from `99c3925` (2026-09-03), `proved (Lean)` by `5893c69`; upstream `answer(True)` | the "yes" direction is the proved one; label updated |
| 130 | OPEN | upstream `answer(True)`, `research solved`, with a Lean link | the "yes" direction is the proved one; label updated |
| 138 | OPEN | upstream records two further questions as solved after the capture | the main question is unaffected |
| 121, 127, 135, 139, 140 | already settled | Lean proofs recorded by the mirror in 2026-08 | no effect |

124 is different: Part 1 was already proved on the page at capture, and the input's label was wrong
then. The proofs behind 123, 125, 126, 130 and the two sub-questions of 138 could not be read in
this container. v2 records them with provenance and labels them unverified. None decides a verdict except
125, where confidence is medium.

## Prior-review audit (`deepmind/ai-review/`)

12 of the 20 problems have an archived prior review: 121, 122, 127, 129, 130, 131, 132, 133, 134, 135, 136
and 140. 123, 124, 125, 126, 128, 137, 138 and 139 have none. Every prior review was written against a
styled copy in `deepmind/deepmind/` (sometimes an earlier state of it), never against the raw
`conjectures/` file reviewed here.

**Right on the core defect, but not applied to the raw corpus.** The prior review found the central defect in
three problems, and the styled copy fixed it while the raw file kept it:

- 132: the factor of two from ordered pairs (the bound `2 * A.card`);
- 133: `sInf` where `sSup` is needed;
- 136: the missing symmetry of the colouring, hedged as "could invalidate". It is settled in this batch:
  all three theorems are false.

References, variants and refactors added to styled copies (121, 127, 129, 130, 131, 134, 140) likewise never
reached the raw files. That is why all 20 raw files have citation defects.

**Missed the defect.**

- 122 was certified as "mathematically correct" while its property is unsatisfiable.
- 127 and 130 praised docstring remarks that are false.
- 135 evaluated the $n=1$ case as true and called the vacuity minor, so the statement is false.
- 129 missed the junk value of `sInf ∅` at $r=1$.

**Wrong or invented bibliographic data**, some of it written into styled copies:

- 121 claimed `[Er38]` is not on the page, and misattributed the even-$k$ result.
- 122 certified citations that contradict the page: [EPS97] as part III (the page has IV), and titles that
  belong to other papers for [Er97] and [Er97e].
- 129 and 136 gave `[Er97b]` as the Erdős–Gyárfás paper in Combinatorica. The site-wide meaning of the key
  is Erdős's Discrete Math. (1997) survey. 130, 131, 132, 133 and 135 attached other wrong titles to
  `[Er97b]`, `[Er97e]`, `[Er75b]` or `[Ta24c]`.
- 134 certified an invented `[Al94]`. The page cites a note by Alon by a link.
- 136 gave `[BCDP22]` the title of a different paper.

**Reuse claims not reproducible.** The pinned upstream clone is partial. Claims about duplicated definitions
in other files could not be checked for 129, 131, 132, 133, 135 and 136, and several named files are absent.
Where the corpus's own copy has the definition, the review says so.

**Mathematical slips.**

- 133: "the set is all of ℕ" for $n=0$.
- 129: two suggested bounds that are false at $n=0$.
- 130: a suggested variant that is not a consequence of Anning–Erdős.
- 122: variants recommended as open that are one-line corollaries.
- 140: intervals said to "differ by at most 1" (they are equal), and the $k$-term conjecture called open "for
  $k\ge5$" although the page gives no status.

The prior reviews' encoding checks were usually right: `sSup` boundedness, coercions, and the equivalence of
a definition with Mathlib's.

## Compile verification

- **Toolchain.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), the version the repository pins, built from
  source in the container.
- **Inputs.** All 20 build with 0 errors and 29 `declaration uses sorry` warnings, one per input theorem.
- **v2 files.** Each was checked with `lake env lean conjectures-v2-sonnet-5-5/N.lean`. All 20 compile with 0
  errors and 84 `declaration uses sorry` warnings, and no other warnings.
- **Axiom audit.** `#print axioms` was run for all 153 theorems in the v2 files. None depends on an axiom
  other than `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. No v2 file declares an `axiom`, and
  none uses `native_decide`. The explicit finite checks use `decide +kernel`.
- **Static checks (Part D).** No input or v2 file has a `sorry` inside a definition, a one-line `:= sorry`, or a
  debug command. Every theorem in the v2 files has a docstring. The only `axiom` among the 40 files is in
  the input of 138.
- **Modules built on demand.** 127 needed `Mathlib.Analysis.SpecialFunctions.Sqrt` for the input, 138 built
  `Mathlib.Combinatorics.HalesJewett`, and 139 built `Mathlib.Combinatorics.Additive.Corner.Roth` with its
  regularity-lemma dependencies (2022 jobs).
- **Limits.** Compilation checks syntax, types and the proofs. The cited literature results are stated as the
  pages word them and were not checked against the papers. Spot checks were done by exhaustive or
  numerical computation (programs in the session scratchpad, none part of the repository):
  - 121: $F_2(N)$ for $N\le20$;
  - 123: divisibility antichains for $n\le900$;
  - 126: subsets of $\{1,\dots,30\}$;
  - 127: all graphs on at most 7 vertices with $m\le21$;
  - 128: the Petersen case (in Lean) and $C_5$ blow-ups;
  - 131: $N\le45$;
  - 132: eight point configurations;
  - 133: $f(2),\dots,f(8)$;
  - 136: symmetric $f(4),\dots,f(9)=5,5,5,7,7,8$, and 5-colourings of ordered pairs for $n\le16$;
  - 137: powerful products for $3\le k\le8$ and $m<2\cdot10^7$;
  - 138: $W(2),W(3),W(4)=3,9,35$;
  - 139: $r_3(N)$ and $r_4(N)$ for $N\le30$.

## Caveats

- **No independent comparison.** There are no Fable, Haiku or Opus reviews for 121–140, so nothing here was
  cross-checked by another model's review.
- **One session, in order.** The pipeline's ideal is a fresh process per problem (`GAME_PLAN.md` §5). These
  reviews ran in one session. The session's context was summarized and resumed at least once, during
  Problem 136, with no effect on the artifacts. Bibliography reused across problems is attributed to its
  original log source.
- **DEFERRED items** (each caps that problem's confidence at medium):
  - 122: the intended hypothesis on $F$ in [EPS97] and [Er97e];
  - 124: [Me04];
  - 125: [Me01] and [HaMe24];
  - 128: [EFRS94], [Kr95], [KeSu06], [NoYe15] and [Ra22];
  - 133 and 134: Alon's note, cited on the page by a link only;
  - 136: whether `[Er97b]` proves the Erdős–Gyárfás bounds;
  - 137: the entries for [Er82c] and [ErSe75], which come from upstream, since no `/latex/137` fetch exists;
  - 138: [ErGr79] and [KoSh16], with no `/latex/138` fetch;
  - 139: [Sz75], [GrTa17], [Er76g] and the title of [LSS24], with no `/latex/139` fetch.
- **Post-capture results unchecked.** The Lean proofs and papers behind the status changes above (123, 125,
  126, 130, 138 and the Lean statuses of 121, 127, 135, 139, 140) were not read.
- **Label normalisation.** These were cleanup commits only, with no finding changed:
  - first-person wording removed from the docstrings of 124, 125 and 126 (`3e77edf2`, `94724ca2`);
  - one first-person phrase reworded in the review of 139 (`c9717cc1`);
  - one `DEFERRED` label removed from the review of 140, where it bore on no check.
- **Quoted first-person text.** The v2 files and reviews contain first-person words only inside verbatim quotes
  of a page remark or of a paper title (for example "if we further have…" in 124, "if we just have…" in 134,
  "my favourite…" in
  several reference titles) or inside quotations of the input's own docstrings that a review flags (for
  example "We axiomatize this classical result" in 138).
- **Site integration not done.** `palomar/build_manifest.py` (`CORPUS_DIRS`) and `site/stamp.py` read only the
  Fable and Haiku directories. Adding `sonnet-5-5-review/` and `conjectures-v2-sonnet-5-5/` (and
  `opus-5-5-review/`) would surface these batches in the explorer. That was out of scope.
