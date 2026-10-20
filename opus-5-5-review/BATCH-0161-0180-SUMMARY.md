---
batch: 0161-0180
reviewer_model: claude-opus-5-5
effort: xhigh
review_date: 2026-10-20
selection: problems 161–180, the 20 problems that follow batch 0141–0160; the user asked for the next batch and for the model change to be noted
model_change: batches 0121–0140 and 0141–0160 were reviewed by Sonnet 5.5 at effort max; this batch is reviewed by Opus 5.5 at effort xhigh (the user's "extra", read as extra-high)
input_artifacts: conjectures/161.lean .. conjectures/180.lean
output_artifacts: conjectures-v2-opus-5-5/N.lean, opus-5-5-review/N.md (N = 161..180)
problems_reviewed: 20
verdict_accept: 0
verdict_accept_with_nits: 14
verdict_needs_revision: 6
confidence_high: 7
confidence_medium: 13
confidence_low: 0
source_recovered: 20
compile_status: pass
---

[AI - Claude Opus 5.5]: Opus 5.5 review batch 0161–0180

# Opus 5.5 review batch 0161–0180

This batch reviews problems 161–180 with the repository's pipeline (`FABLE_REVIEW.md` and `FABLE_REVIEW_RUN.md`).

- **Model change.** The two previous batches (0121–0140 and 0141–0160) were reviewed by **Sonnet 5.5 at effort max**.
  This batch was reviewed by **Opus 5.5 at effort xhigh**: the user switched the model to Opus 5.5 and asked for "extra"
  effort, which the model read as the `xhigh` level. Every review records `reviewer_model: claude-opus-5-5` and
  `effort: xhigh`.
- **Outputs.** The reviews are in `opus-5-5-review/`, alongside the earlier Opus 5.5 batches (91–120 and 1101–1110), and the
  fixed files are in `conjectures-v2-opus-5-5/`. The inputs in `conjectures/` are untouched.
  - Each v2 file keeps the input's definitions and statements byte-identical, except where a defect requires a change:
    161, 162, 169, 172, 177 and 180.
- **Order.** Problems were reviewed one at a time, in numerical order. Each was committed separately (subject `Opus 5.5
  review N: …`) and pushed before the next one started. Two follow-up commits recovered citations first marked DEFERRED
  (165, 169).
- **Independence.** No Fable, Haiku, Sonnet or earlier Opus review exists for any of these 20 problems, so there is no
  cross-reviewer comparison. Archived DeepMind reviews exist for 17 of the 20, and Part E of each review audits them.
- **Compiled.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), built from source in the container. All 20 inputs and all
  20 v2 files compile.

## Headline numbers

| Metric | Value |
|---|---|
| ACCEPT / ACCEPT WITH NITS / NEEDS REVISION | 0 / 14 / 6 |
| Confidence high / medium / low | 7 / 13 / 0 |
| Source page recovered | 20/20 (page captures in the session logs) |
| Status at capture | OPEN 12 (161, 162, 165, 168, 169, 170, 172, 173, 174, 176, 177, 180), FALSIFIABLE 1 (167), PROVED 7 (163, 164, 166, 171, 175, 178, 179) |
| Status now (mirror `b916d95`) | 180 is `disproved (Lean)`; 164, 171, 175 and 178 are `proved (Lean)`; the rest are unchanged |
| Statements **false as written** (refuted in Lean) | 3 problems, 4 theorems: 162 (endpoint $\alpha=1/2$), 177 (both stated "known bounds"), 180 (the "yes" answer refuted by Hunter's family) |
| Statement that is not the page's question | 161: it asserts the easy, known upper bound instead of Erdős's guess (a lower bound) |
| Weakened statement | 172: subsets with $\lvert S\rvert\ge2$ only, which drops the elements of $A$ |
| Definition defect | 169: the van der Waerden number is `Nat.find` of a lemma proved by `sorry`; v2 proves the lemma from Mathlib's Hales–Jewett theorem |
| Inputs with a citation defect | 20/20: 19 cite keys they never define, and 169 cites nothing |
| Input declarations kept byte-identical in v2 | 14 of 20 problems |
| Theorems: inputs → v2 | 26 → 161 (the extra 135 are page-recorded variants, reductions, helpers and Lean checks of the encoding) |
| v2 compile | 20/20 with 0 errors and no warning other than `declaration uses sorry` (72 of those) |
| `sorry` in v2 | 72 of the 161 theorems contain one, and none inherits one from another declaration. The other 89 are proved with `propext`, `Classical.choice` and `Quot.sound` only |

## Per-problem results

"Exact" means the main statement was judged a faithful encoding and kept byte-identical.

| # | Verdict | Conf. | Part A finding | Other findings |
|---|---|---|---|---|
| 161 | **NEEDS REV** | med | asserts the classical random-colouring upper bound, not Erdős's guess (a lower bound $F^{(t)}(n,\alpha)\gg(\log n)^{1/(t-1)}$); the page prints the two inequalities the other way round | 2 undefined keys; the input statement is proved in Lean from the random bound; `F_balanced` is 0 at $\alpha=0$ |
| 162 | **NEEDS REV** | high | false at the endpoint $\alpha=1/2$ ($F(n,1/2)=n+1$, refutation proved in Lean); v2 restricts to $\alpha<1/2$ | the definition docstring's "largest $k$" should be "smallest"; 1 undefined key |
| 163 | NITS | med | none; exact (Burr–Erdős, PROVED by Lee) | 3 undefined keys; `containsCopy` proved equal to Mathlib's `⊑`; [BuEr75] DEFERRED |
| 164 | NITS | med | none; exact (Erdős primitive set conjecture, PROVED by Lichtman) | 4 undefined keys; "maximised at the primes" proved from the inequality; the statement needs the prime sum to converge |
| 165 | NITS | high | none; exact ($R(3,k)\sim ck^2/\log k$ for some $c$, open) | undefined keys; the known bounds confine $c$ to $[1/2,1]$ (proved in Lean); $R(3,k)$ for $k\le4$ by search |
| 166 | NITS | high | none; exact ($R(4,k)\gg k^3/(\log k)^{O(1)}$, PROVED) | 7 undefined keys; the natural exponent is equivalent to a real one, and the AKS bound forces $\alpha\ge2$ (both proved) |
| 167 | NITS | med | none; exact (Tuza's conjecture, falsifiable) | 3 undefined keys; the trivial $3k$ bound follows from the hypothesis, and $K_4$ makes $2k$ optimal (proved); the DeepMind copy's [Er88] is a different paper |
| 168 | NITS | med | none; exact (the limit of $F(N)/N$ is irrational, open) | undefined keys; the value 0.800965 is credited to [GSW77] instead of Eberhard; the limit is reproduced in $[0.8009644,0.8009664]$ |
| 169 | **NEEDS REV** | high | `vanDerWaerdenNumber` rests on a `sorry` lemma (`#print axioms` lists `sorryAx`); v2 proves van der Waerden from Hales–Jewett | no references at all; $f(k)\ge\frac12\log W(k)$ proved in Lean; the prior review's equivalence with Problem 3 is misstated |
| 170 | NITS | med | none; the definitions are exact, and the theorem asserts the value $\sqrt3$ suggested by Pegg | 4 undefined keys (all DEFERRED); $F(N)$ checked to $N=40$; $N\le\binom{F(N)}2$ proved |
| 171 | NITS | med | none; exact (density Hales–Jewett, PROVED) | 4 undefined keys; `IsCombLine` proved equal to Mathlib's `Line`, so the statement equals upstream's |
| 172 | **NEEDS REV** | med | weakened: only subsets with $\lvert S\rvert\ge2$, so the elements of $A$ need not share the colour; v2 uses nonempty $S$ | 5 undefined keys; $0\in A$ proved harmless; Hindman, Moreira and Alweiss added |
| 173 | NITS | med | none; exact (at most one exceptional triangle, open) | 5 undefined keys; Heron's formula proved, so congruent copies of triangles are triangles |
| 174 | NITS | med | none; the theorem asserts Graham's characterisation (spherical ⟺ Ramsey), labelled as such | 4 undefined keys; the [LRW12] alternative added; collinear triples proved non-spherical |
| 175 | NITS | high | none; exact ($\binom{2n}n$ not squarefree for $n\ge5$, PROVED) | 5 undefined keys; $n\ge5$ sharp; $f(n)\le\log_2(2n)$ proved; 786 confirmed to $10^7$ |
| 176 | NITS | med | none; exact (three open questions on $N(k,\ell)$) | 3 undefined keys; junk value for $\ell>k$ and two cases of Spencer's formula proved |
| 177 | **NEEDS REV** | high | both "known bounds" are false: Roth's for every $d$ (refuted by $(-1)^{\lfloor n/d_0\rfloor}$) and Beck's at $d=1,2$; refutations proved | 2 undefined keys; van der Waerden unboundedness proved from Hales–Jewett |
| 178 | NITS | med | none; exact (Beck's balancing theorem, PROVED) | 4 undefined keys; one sequence balanced with bound 1 (proved); the DeepMind review's [Be81] and [Be17] are wrong |
| 179 | NITS | med | none; exact (Fox–Pohoata, PROVED) | 1 undefined key and no module docstring; the trivial $N^2$ bound proved; `numAP A 1` is $\lvert A\rvert\cdot\max A$ |
| 180 | **NEEDS REV** | high | asserts the "yes" answer that Hunter's star-and-matching family refutes (the input's docstring says so); the negation is proved in Lean | 1 undefined key; mirror now `disproved (Lean)`; the cyclic-family counterexample recorded |

NITS is short for ACCEPT WITH NITS. Every v2 file also adds a module docstring, page-recorded variants, reductions between
them, or Lean proofs of what the review argues. Each variant is labelled PROVED, SOLVED, OPEN or DISPROVED with its source.

## Defect classes

| Class | Count | Problems |
|---|---|---|
| undefined-citation-key | 19 | 161–168, 170–180 |
| missing-references | 1 | 169 |
| wrong-target-statement | 1 | 161 |
| known-result-as-open-problem | 1 | 161 |
| false-at-endpoint | 1 | 162 |
| misleading-docstring-remark | 1 | 162 |
| misattributed-result | 1 | 168 |
| sorry-in-definition | 1 | 169 |
| weakened-statement | 1 | 172 |
| wrong-quantifier-structure | 1 | 177 |
| false-at-small-parameters | 1 | 177 |
| wrong-polarity | 1 | 180 |

Four patterns stand out:

- **Statements labelled as known results that are false as written (162, 177, 180).** In each case the defect is proved in
  Lean.
  - 162 includes the endpoint $\alpha=1/2$, where the defining condition cannot hold for both colours.
  - 177 states Roth's lower bound "for every $d$". One sequence can be balanced along any single difference; v2 proves this
    with $(-1)^{\lfloor n/d_0\rfloor}$. It also states Beck's upper bound for every $d\ge1$, which fails at $d=1$ and $2$.
  - 180 asserts the Erdős–Simonovits property for every finite family, while its own docstring cites Hunter's counterexample.
    v2 proves it: a graph with two distinct edges contains a 2-edge star or a 2-edge matching, while matchings and stars avoid
    one of them and have unboundedly many edges.
- **Readings of the question (161, 170, 172, 174).**
  - 161 states the easy known direction instead of Erdős's guess; the page itself prints the inequalities reversed.
  - 172 drops the singletons from "sums and products of distinct elements", against the cited results and upstream.
  - 170 and 174 assert one conjectured answer to an open "find" or "characterise" question. The model accepts this when the
    file labels the choice and the page singles it out ($\sqrt3$, Graham's conjecture). v2 records the alternatives.
- **Van der Waerden from Mathlib.** Mathlib's Hales–Jewett theorem gives the finite van der Waerden theorem in a few dozen
  lines, by summing coordinates along a combinatorial line. The model used it three times: to remove the `sorry` behind
  `vanDerWaerdenNumber` (169), to prove the page's "trivial" bound $f(k)\ge\frac12\log W(k)$ (169), and to prove that no
  $\pm1$ sequence has bounded discrepancy (177). The Sonnet batch proved van der Waerden by compactness for Problem 138.
- **Encodings validated in Lean.** In the 14 accepted problems the defects are the citations and the missing status. v2 adds
  proofs that the encodings behave as intended:
  - equality with Mathlib's notions: `containsCopy` = `⊑` (163), `IsCombLine` = `Combinatorics.Line` (171), `centralBinom` (175);
  - equivalent forms: a real exponent (166), positive integers only (172);
  - sharpness and non-triviality: $K_4$ (167), $n\ge5$ (175), $\alpha\ge2$ (166), $c\in[1/2,1]$ (165), non-spherical collinear
    triples (174);
  - small values by `decide`: $F$ in 168 and 170, `numAP` in 179;
  - Spencer's formula in two cases (176).

## Status changes after capture

Captures date from 2026-02-20 to 2026-03-05. The mirror snapshot is `b916d95`, and upstream `formal-conjectures` is at
`df3f12d`.

| # | At capture | Now | Effect on the input |
|---|---|---|---|
| 180 | OPEN (with Hunter's counterexample on the page) | mirror `disproved (Lean)` (2026-08-02); upstream `answer(False)` for the cyclic-family version, citing [OpenAI26] | the input's "yes" was already refuted at capture by the page's own remark; v2 proves the refutation |
| 164, 171, 175, 178 | PROVED | mirror `proved (Lean)`; upstream links Lean proofs (`plby/lean-proofs`) | none; the statements are the proved direction and agree with upstream |
| 163, 166 | PROVED | mirror `formalized: yes`; upstream has the statements | none |
| 165 | OPEN | open; a 2026-03-15 summary lists an extra key [Er78] that the capture lacks | none |

The other 11 problems are unchanged in status. The Lean proofs that upstream and the mirror link were not read.

## Prior-review audit (`deepmind/ai-review/`)

17 of the 20 problems have an archived prior review; 168, 170 and 172 have none. Every prior review was written against a styled
copy in `deepmind/deepmind/`, never against the raw `conjectures/` file reviewed here.

**Missed the defect.**

- 177: certified both false theorems as correct ("for every coloring and every $d$"; "correctly formalizes Beck's result").
- 169: called the `sorry` behind `vanDerWaerdenNumber` "expected since it is a non-trivial theorem".
- 162, 161: see those reviews; the endpoint and the reversed inequalities were not caught.
- 180: the styled copy has the right polarity (`answer(False)`), but the raw input kept the wrong one.

**Wrong or unsupported bibliographic data.**

- 167: the styled copy's [Er88] is a 1985 paper on chromatic numbers; the site's [Er88] is a 1988 Discrete Math. paper.
- 171: [ErGr79] "matches website", with a subtitle that differs from upstream's.
- 175: claimed the site does not use [Er79] and [ErGr80]; the page's heading cites both.
- 178: gave titles for [Be81] and [Be17] that are not the site's entries.
- 169: dated [Wr84] to 2024, and said Problem 169 is equivalent to Problem 3. The page says Problem 3 is equivalent to the
  finiteness of $f(k)$.

**Mathematical slips.** 166: the reason given for $R(4,1)=1$ is wrong (the value is right). 173: "SSS only holds for
non-degenerate triangles". 180: "the set is nonempty (the empty graph gives 0 edges)", which fails when a member is edgeless.

The checklist reviews (`deepmind/reviews/`) mostly enforce upstream's `answer()` convention. This corpus accepts an asserted
"yes" direction for open yes/no questions, as earlier batches did.

## Compile verification

- **Toolchain.** Lean 4.28.0 and Mathlib `v4.28.0` (`8f9d9cff6b`), the version the repository pins, built from source in the
  container. Problem 168 imports `Mathlib.NumberTheory.Real.Irrational`, which had not been built; `lake build` of that module
  fixed the input's first compile failure, an environment issue only.
- **Inputs.** All 20 build with 0 errors and 25 `declaration uses sorry` warnings: 25 of the 26 input theorems and
  lemmas, including 169's `vdw_exists`, which the definition `vanDerWaerdenNumber` uses. The 26th, 170's
  `differenceBasis_exists`, is proved in the input.
- **v2 files.** Each was checked with `lake env lean conjectures-v2-opus-5-5/N.lean`. All 20 compile with 0
  errors and 72 `declaration uses sorry` warnings, and no other warnings.
- **Axiom audit.** `#print axioms` was run for all 161 theorems in the v2 files. 89 depend only on `propext`,
  `Classical.choice` and `Quot.sound`; the other 72 also depend on `sorryAx`, and none depends on any other axiom.
  No v2 file declares an `axiom`, and none uses `native_decide`. The finite checks use `decide` or `decide +kernel`
  (165, 168, 170, 175, 179).
- **Static checks (Part D).** No v2 file has a `sorry` inside a definition, a one-line `:= sorry`, or a debug command, and all 201
  declarations in the v2 files have a docstring. Among the inputs, 169's `vanDerWaerdenNumber` depends on a `sorry` lemma
  (fixed in v2). No input declares an `axiom`.
- **Computations** (programs in the session scratchpad, none part of the repository):
  - 165: $R(3,k)$ for $k\le4$ (3, 6, 9) and $R(3,5)\ge14$, by exhaustive search;
  - 168: $F(N)$ for $N\le22$ by brute force, and the limit from the [GSW77] formula, in $[0.800964494,0.800966372]$;
  - 170: the minimal sparse ruler sizes for $N\le40$;
  - 175: square-freeness of $\binom{2n}n$ and odd prime squares for $n\le10^7$.

  The other 16 problems needed no computation beyond their Lean proofs.

## Caveats

- **No independent comparison.** There are no other reviews of 161–180 in this repository, so nothing here was
  cross-checked by another model's review.
- **One session, in order.** The pipeline's ideal is a fresh process per problem. These reviews ran in one session. Its
  context was summarized twice (during 165 and during the final re-verification), and the worker process was restarted
  once (during 180). All 20 inputs and all 20 v2 files were recompiled, and the axiom audit run, after the last review
  commit.
- **DEFERRED items.** Each caps that problem's confidence at medium, except where the verdict rests on a defect proved in Lean
  (162, 169, 177, 180).
  - [ErGr79] in 168, 169, 171–174 and 176–179: v2 uses upstream's entry from its Problem 171 file.
  - 161: the papers behind the remarks;
  - 163: [BuEr75];
  - 164: [Er76g] and [Er86];
  - 167: [Ha99] and [KaPa22];
  - 168: [GSW77];
  - 170: all four keys;
  - 172: [Hi80], [Mo17], [Al23] and [BoSa22];
  - 180: [ErSi82].
  - Several keys first marked DEFERRED were recovered from other problems' bibliographies (165, 169).
- **Corrected forms not checked against papers.** v2's corrected statements of Roth's and Beck's bounds (177) and the
  constant form of Beck's 2017 bound (178) follow the pages' summaries; the docstrings say so.
- **Quoted first-person text.** First-person words appear only inside verbatim quotes of page remarks or paper titles (for
  example "Some of my favorite problems and results", "it seems certain that the answer is affirmative" in 178, "feels sure"
  in 175).
- **Log line numbers.** The Addenda cite session-log records with 1-based line numbers.
