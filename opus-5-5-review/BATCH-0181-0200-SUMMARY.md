---
batch: 0181-0200
reviewer_model: claude-opus-5-5
effort: xhigh
review_date: 2026-11-05
selection: problems 181–200, the 20 problems that follow batch 0161–0180; the user asked for the next batch
model: unchanged from batch 0161–0180 (Opus 5.5 at effort xhigh); batches 0121–0160 were Sonnet 5.5 at effort max
input_artifacts: conjectures/181.lean .. conjectures/200.lean
output_artifacts: conjectures-v2-opus-5-5/N.lean, opus-5-5-review/N.md (N = 181..200)
problems_reviewed: 20
verdict_accept: 0
verdict_accept_with_nits: 12
verdict_needs_revision: 8
confidence_high: 3
confidence_medium: 17
confidence_low: 0
source_recovered: 20
compile_status: pass
---

[AI - Claude Opus 5.5]: Opus 5.5 review batch 0181–0200

# Opus 5.5 review batch 0181–0200

This batch reviews problems 181–200 with the repository's pipeline (`FABLE_REVIEW.md` and `FABLE_REVIEW_RUN.md`).

- **Model.** Opus 5.5 at effort `xhigh`, as in batch 0161–0180 (which noted the change from Sonnet 5.5 at effort max). Every
  review records `reviewer_model: claude-opus-5-5` and `effort: xhigh`.
- **Outputs.** The reviews are in `opus-5-5-review/` and the fixed files in `conjectures-v2-opus-5-5/`. The inputs in
  `conjectures/` are untouched.
  - Each v2 file keeps the input's declarations byte-identical, except where a defect requires a change. The theorem statement
    changes in 183, 187, 189, 190, 193, 196 and 197; in 198 only the proof changes (the `sorry` is replaced by a proof).
- **Order.** Each problem has its own commit (subject `Opus 5.5 review N: …`), made and pushed in numerical order. One follow-up
  commit corrects Part E of 192 and 199 (the DeepMind styled copy and checklist exist for both). The drafting order differed
  from the commit order; see the caveats.
- **Independence.** No Fable, Haiku, Sonnet or earlier Opus review exists for any of these 20 problems. DeepMind artifacts exist for
  12 of the 20 (181–187, 190–193, 199), and Part E of each of those reviews audits them.
- **Compiled.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), built from source in the container. All 20 inputs and all 20 v2
  files compile.

## Headline numbers

| Metric | Value |
|---|---|
| ACCEPT / ACCEPT WITH NITS / NEEDS REVISION | 0 / 12 / 8 |
| Confidence high / medium / low | 3 / 17 / 0 |
| Source page recovered | 20/20 (page captures in the session logs) |
| Status at capture | OPEN 11 (181, 183, 184, 187, 188, 190, 193, 195, 196, 197, 200), PROVED 3 (182, 185, 191), SOLVED 2 (186, 192), DISPROVED 4 (189, 194, 198, 199) |
| Status changes after capture | refuting the input: 183, 193, 196; solved in the asserted direction: 181, 184, 190; Lean proofs recorded: 185, 191, 192, 194, 199 |
| Statement false as written, refuted in Lean | 189: the page records the answer no, the input asserts yes; v2 proves the negation with a 25-colouring |
| Statements refuted after capture | 183, 193, 196 (upstream or mirror records; not checked here) |
| Not the page's question | 187 (an unrecorded guess $f(d)\gg\log d$), 195 (a lower bound for a value question) |
| Wrong definitions | 190 (rainbow progressions of length 3, not $k$), 197 ("monotone" counts only increasing progressions) |
| Docstring errors | 185 (combinatorial lines called equivalent to the page's geometric lines), 192 (length 7 for abelian squares; it is 8) |
| Inputs with a citation defect | 20/20 |
| Input declarations kept byte-identical in v2 | 12 of 20 problems, and 198's statement |
| Theorems: inputs → v2 | 21 → 120 |
| v2 compile | 20/20 with 0 errors and no warning other than `declaration uses sorry` (55 of those) |
| `sorry` in v2 | 55 of the 120 theorems contain one, and none inherits one from another declaration. The other 65 are proved with `propext`, `Classical.choice` and `Quot.sound` only |
| Input theorems proved in v2 | 198 (fully); 189's refutation (fully) |

## Per-problem results

"Exact" means the main statement was judged a faithful encoding and kept byte-identical.

| # | Verdict | Conf. | Part A finding | Other findings |
|---|---|---|---|---|
| 181 | NITS | med | none; exact (Burr–Erdős $R(Q_n)\ll2^n$; upstream now records it solved) | undefined key; Erdős–Szekeres proved, so the `sInf` is not junk; $2^n\le R(Q_n)\le4^{2^n}$ proved |
| 182 | NITS | high | none; exact (Janzer–Sudakov) | undefined keys; the theorem proved to imply the page's $n^{1+o(1)}$ answer; three sanity checks of the definition |
| 183 | **NEEDS REV** | med | asserts a finite limit of $R(3;k)^{1/k}$; upstream and the mirror now record $\to\infty$ | the diagonal convention gives $R(3;0)=1$, so the page's recursion fails at $k=1$ (proved) |
| 184 | NITS | med | none; exact (Erdős–Gallai; upstream now records it solved) | undefined keys; the trivial decomposition proved |
| 185 | NITS | high | none; exact (DHJ(3)), stronger than the page's statement | docstring calls combinatorial and geometric lines equivalent; DHJ(3) proved to imply the page's $f_3(n)=o(3^n)$; maxima 18 and 16 at $n=3$ |
| 186 | NITS | med | none; exact ($F(N)=N^{1/4+o(1)}$) | undefined keys; the recorded bounds proved to give the theorem; three `decide` checks |
| 187 | **NEEDS REV** | med | asserts $f(d)\gg\log d$, a guess the page does not make | van der Waerden with large differences proved from Hales–Jewett |
| 188 | NITS | med | none; exact as an existence statement for a value question | $k=1$ impossible and Alon's remark proved |
| 189 | **NEEDS REV** | high | asserts the "yes" answer the page records as false; v2 proves the negation in Lean | — |
| 190 | **NEEDS REV** | med | rainbow progressions of length 3 instead of $k$; $H_3(2)=3$, the page's $H(2)=2$ (both proved) | mirror records the page's question solved |
| 191 | NITS | med | none; exact (Rödl) | trivial for $C\le1/\log2+1/\log3$ (proved); [CFS13] proved to imply the theorem |
| 192 | NITS | med | none; exact in abelian-square form | page and docstring say length 7 suffices; `cbcacbc` refutes it (`decide`) |
| 193 | **NEEDS REV** | med | asserts collinear triples; upstream and the mirror now record the answer no | degenerate triples proved collinear |
| 194 | NITS | med | none; exact (negative answer) | $k=3$ settles all $k\ge3$ (proved) |
| 195 | **NEEDS REV** | med | asserts the lower bound $k\ge3$ for "what is the largest $k$" | Geneson from Adenwalla and monotonicity in $k$ proved |
| 196 | **NEEDS REV** | med | asserts monotone 4-term progressions; upstream now records the answer no | DEGS77's 3-term theorem proved |
| 197 | **NEEDS REV** | med | "monotone" means increasing only, which makes the statement elementary | the two-sided statement proved to imply the input's |
| 198 | NITS | med | none; exact (negative answer) | **the theorem proved in Lean** with the AlphaProof set |
| 199 | NITS | med | none; exact (Baumgartner) | sanity checks |
| 200 | NITS | med | none; exact ("yes" asserted, open) | `longestPrimeAP` proved to be a true maximum |

NITS is short for ACCEPT WITH NITS. Every v2 file also adds a module docstring with the status at capture and after, the
references, and the encoding notes.

## Defect classes

| Class | Count | Problems |
|---|---|---|
| undefined-citation-key | 20 | 181–200 |
| wrong-polarity | 4 | 183, 189, 193, 196 |
| wrong-target-statement | 2 | 187, 195 |
| wrong-definition | 2 | 190, 197 |
| misleading-docstring-remark | 2 | 185, 192 |

Five patterns stand out:

- **Post-capture refutations (183, 193, 196).** Three open problems in this batch were answered "no" between the capture
  (February–March 2026) and November 2026, against the asserted "yes" direction. v2 states the recorded answers with `sorry`
  and keeps the input's statements as variants or negations. 183's record is corroborated by both upstream and the mirror, 193's
  likewise; 196's only by upstream (the mirror still lists it as open). For 193 the refutation carries over to the input's
  injective walks only if the counterexample walk is injective, which was not checked.
- **A refutation at capture, proved (189).** The input's docstring says "This conjecture is false", yet the theorem asserts it.
  v2 proves the negation with a 25-colouring of Kovač's kind: colour $z$ by $\lfloor\operatorname{Re}z^2/s\rfloor$ and
  $\lfloor\operatorname{Im}z^2/s\rfloor$ modulo 5 with $s=7/10$. For a rectangle the alternating sum of $z^2$ has modulus
  $2\cdot$area, and for one colour that modulus avoids $2$.
- **Readings that change the problem (185, 190, 197).** "Three points on a line" are collinear points, not combinatorial lines
  (185, harmless because DHJ(3) implies the page's statement, but the docstring calls them equivalent). The "rainbow progression"
  of canonical Ramsey theory has $k$ terms, not 3 (190). "Monotone" includes decreasing (197).
- **Open value questions (187, 188, 195).** For "find the best $f(d)$" and "what is the largest $k$", the inputs assert an
  unrecorded guess (187) and a lower bound (195); both are flagged, as Problems 148 and 112 were. 188's existence statement for
  "the smallest $k$" is accepted with a nit, as Problem 165's was.
- **Van der Waerden and Ramsey from scratch.** Mathlib has no graph Ramsey theorem; 181 proves the Erdős–Szekeres bound. 187 and
  188 derive van der Waerden for 2-colourings of $\mathbb Z$ from Mathlib's Hales–Jewett theorem, as earlier batches did.

## Status changes after capture

Captures date from 2026-02-20 to 2026-03-05. The mirror snapshot is `c443d8c` (2026-11-03), and upstream `formal-conjectures` is
at `2befc3a` (2026-11-04). Neither the papers nor the Lean proofs they link were read.

| # | At capture | Now | Effect on the input |
|---|---|---|---|
| 183 | OPEN (\$250) | mirror `solved (Lean)` (2026-08-01); upstream: $R(3;k)^{1/k}\to\infty$ [OpenAI26] | the asserted finite limit is refuted |
| 193 | OPEN | mirror `disproved (Lean)` (2026-09-04); upstream: the negation for infinite-range walks [CaKa26] | refuted, if the counterexample walk is injective |
| 196 | OPEN | upstream: the negation [Ho26], with Lean proofs; mirror still `open` | refuted per upstream |
| 181 | OPEN | upstream: solved [OpenAI26], with a Lean proof; mirror still `open` | none; the asserted direction |
| 184 | OPEN | upstream: solved [OAI26a], with a Lean proof; mirror still `open` | none; the asserted direction |
| 190 | OPEN | mirror `solved` (2026-06-02), `solved (Lean)` (2026-09-15) | none for the page's question; the input states a different function |
| 185, 191 | PROVED | mirror `proved (Lean)` | none |
| 192 | SOLVED | mirror `solved (Lean)` | none |
| 194, 199 | DISPROVED | mirror `disproved (Lean)` | none |

The other 8 problems are unchanged in status (189 and 198 were already DISPROVED (LEAN) at capture).

## Prior-review audit (`deepmind/ai-review/`)

12 of the 20 problems have an archived prior review (181–187, 190–193, 199); 188, 189 and 194–198, 200 have no DeepMind artifacts.
Every prior review was written against a styled copy in `deepmind/deepmind/`.

**Missed the defect.**

- 185: called the page's lines combinatorial lines and the density statement "equivalent to $f_3(n)=o(3^n)$".
- 190: called 3-term rainbow progressions "the standard formulation" in canonical Ramsey theory.
- 192: suggested formalizing the (false) length-7 bound as a variant.
- 187: called $f(d)\gg\log d$ "the lower-bound conjecture implicit in Erdős Problem 187".

**Wrong or unsupported bibliographic data.**

- 182: invented titles for [Er78] and [CJMM24b].
- 184: said [EGP66] is *On the maximal number of vertices representing the edges of a graph* and "matches"; the site's [EGP66] is
  *The representation of a graph by set intersections*.
- 186: gave [PhZa24] the title of a different paper.
- 193: gave [GeRa79] a different title and journal.
- 181: said [BuEr75] matches the website, which has no entry for it.
- 191, 199: said the site gives no bibliographic details; its `/latex` pages do.

**Mathematical slips.** 182: "`Nonempty` is automatically satisfied for $k\ge3$" (the empty graph is vacuously $k$-regular) and
"`Real.log x` returns 0 for $x\le0$". 183: a self-contradictory analysis of $k=0$ (the set is $\{n\ge1\}$ and $R(3;0)=1$).
190: "`HasMonoAP` is vacuously satisfied for $k=0$" (it needs $N\ge1$).

## Compile verification

- **Toolchain.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), the version the repository pins. The container started without
  Lean; the toolchain was installed from the Lean GitHub release, and Mathlib was built from source, since the Mathlib cache host
  is blocked by the network policy.
- **Inputs.** All 20 build with 0 errors and 21 `declaration uses sorry` warnings, one per input theorem (192 has two theorems).
- **v2 files.** Each was checked with `lake env lean conjectures-v2-opus-5-5/N.lean`. All 20 compile with 0 errors and 55
  `declaration uses sorry` warnings, and no other warnings.
- **Axiom audit.** `#print axioms` was run for all 120 theorems in the v2 files. 65 depend only on `propext`,
  `Classical.choice` and `Quot.sound`; the other 55 also depend on `sorryAx`, and none depends on any other axiom. No v2 file
  declares an `axiom`, and none uses `native_decide`. The finite checks use `decide` (183, 186, 192, 195, 200).
- **Static checks (Part D).** No input or v2 file has a `sorry` inside a definition, a one-line `:= sorry`, or a debug command,
  and all 164 declarations in the v2 files have a docstring. No input declares an `axiom`.
- **Computations** (programs in the session scratchpad, none part of the repository):
  - 185: the largest subsets of $\{0,1,2\}^n$, $n\le3$, avoiding combinatorial lines and avoiding three collinear points
    (2/2, 6/6, 18/16);
  - 192: abelian-square-free words over two letters (longest 3) and three letters (118 words, longest 7).

  The other 18 problems needed no computation beyond their Lean proofs.

## Caveats

- **No independent comparison.** There are no other reviews of 181–200 in this repository.
- **Drafting ahead of compilation.** The container started fresh, and Mathlib had to be built from source (about an hour). While it
  built, the reviews and v2 files were drafted in numerical order; the worker was also restarted once mid-batch, which stopped the
  build. Once Mathlib was ready, every v2 file was compiled and fixed (imports and small proof repairs in 182, 184, 187, 188,
  193–195 and 198), and only then were the 20 problems committed and pushed one at a time, in order. All 40 files were
  recompiled, and the axiom audit run, after the last review commit.
- **DEFERRED items.** Each caps that problem's confidence at medium, except where the verdict rests on a defect proved in Lean
  (189).
  - [ErGr79] in 186–188 and 190–200: v2 uses upstream's entry from its Problem 171 file.
  - 181: [BuEr75] (two different titles in the archived sources);
  - 183: [Er61] (the site's entry is taken from `/latex/511`; upstream gives another paper);
  - 184: [Er76] and [Er83b];
  - 188, 189, 194–196, 198: no `/latex` fetch, so [EGMRSS75], [Ts17], [Ko23], [Gr80], [ABJ11], [Ge19], [Ad22], [DEGS77], [Ho26]
    and [Ba75] come from upstream.
- **Post-capture results not read.** The refutations recorded for 183, 193 and 196, and the solutions recorded for 181, 184 and
  190, were not read; the verdicts follow upstream and the mirror, with medium confidence.
- **Arguments not formalized.** 197's block construction (the input's statement is elementary) and 192's Part 1 (every ternary
  word has an abelian square) are argued or computed in the reviews, not proved in Lean.
- **Quoted first-person text.** First-person words appear only inside quotations: paper titles (for example "On the
  combinatorial problems which I would most like to see solved"), the page remarks quoted in the module docstrings of 184 and
  189 ("if we do not require", "if we replace"), the input's own docstring of `IsNonAveraging`, kept as written in 186 ("we
  have"), and the input docstring quoted in the review of 195 ("We state the problem as"). They are flagged here for the
  user's review rather than reworded.
- **Log line numbers.** The Addenda cite session-log records with 1-based line numbers.
- **Site integration.** `palomar/build_manifest.py` and `site/stamp.py` do not read `opus-5-5-review/` or
  `conjectures-v2-opus-5-5/`. Adding them was left out of scope.
