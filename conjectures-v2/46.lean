import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finite.Defs

open Finset BigOperators

/--
Erdős Problem #46 [Er77c] [ErGr80, p.36] [Er92c] [Er95] [Er96b] [Er97c] — PROVED (LEAN)
(erdosproblems.com/46, page last edited 20 December 2025, accessed 2026-02-22):

"Does every finite colouring of the integers have a monochromatic solution to
1 = ∑ 1/nᵢ with 2 ≤ n₁ < ⋯ < n_k?"

The answer is yes, as proved by Croot [Cr03] — indeed, there are infinitely many
disjoint such monochromatic solutions (see the variants below).

Status and provenance:
- Page banner at capture: PROVED (LEAN), tooltip "This has been solved in the
  affirmative and the proof verified in Lean."
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "proved (Lean)", last update
  2025-12-29; no prize; OEIS: N/A; tags: number theory | unit fractions |
  ramsey theory.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/46.lean,
  present at HEAD dd1c2beb, 2026-08-16) marks `erdos_46` as `research solved`
  with a `formal_proof using lean4 at
  https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos46.lean`
  attribute, and states `answer(True) ↔` the same proposition as below (with the
  colouring encoded as `𝓒 : ℕ → ℕ` of finite range and monochromaticity as
  `(𝓒 '' S).Subsingleton`). The capture's "Formalised statement? No" line is
  stale — superseded by the mirror's `formalized: yes` (2026-08-03) and the
  upstream file.
- The direct assertion below is the proved affirmative direction of the page's
  yes/no question, per this corpus's convention for solved problems.

Encoding notes:
- "Every finite colouring" is encoded polymorphically as `(α : Type*)
  [Finite α] (c : ℕ → α)`; upstream uses a finite-range `𝓒 : ℕ → ℕ`. These are
  equivalent: a finite-range colouring factors through a finite type, and any
  `c : ℕ → α` with `α` finite has the same monochromatic sets as its
  finite-range companion obtained by post-composing with an injection `α ↪ ℕ`.
- The colouring is given on all of ℕ although the problem colours the integers
  ≥ 2 (only those can occur in a solution). Equivalent: every colouring of
  {2, 3, ...} extends to ℕ without changing finiteness, the extra values at
  0 and 1 cannot enter any witness S, and restriction preserves colourings.
- `S.Nonempty` is redundant — the empty sum is 0 ≠ 1, so the reciprocal-sum
  condition already forces S ≠ ∅ — but harmless; it is kept for readability.
- `Finset ℕ` gives distinctness of the nᵢ (the source's n₁ < ⋯ < n_k without
  any ordering data, which a set does not need); the reciprocal sum is computed
  exactly in ℚ. No division by zero can occur inside a witness (all n ≥ 2), and
  ℚ's 1/0 = 0 convention is harmless regardless.

Remarks from the source page:
- The answer is yes, as proved by Croot [Cr03] — indeed, there are infinitely
  many disjoint such monochromatic solutions.
- "In [ErGr80] they also ask for a monochromatic representation of any
  a/b > 0. This follows from the case of 1 — indeed, consider the induced
  colouring of {n/b : b ∣ n}. By the above there are a solutions to
  1 = ∑ᵢ 1/(nᵢ/b), and hence a solutions to 1/b = ∑ᵢ 1/nᵢ, where all nᵢ are
  distinct (across the a many solutions). Summing across all variables then
  yields a/b = ∑ⱼ 1/mⱼ where all mⱼ are distinct and the same colour, as
  required." (The page's "by the above" invokes the infinitely-many-disjoint
  strengthening; the plain single-solution statement also suffices via a
  finite colour-refinement argument — give each already-used integer its own
  fresh colour and re-apply; a monochromatic solution of the induced problem
  has ≥ 2 elements, so it cannot sit inside a fresh singleton class.)
- See also [298].

References (recovered from the original pipeline's WebFetch of
erdosproblems.com/latex/46, preserved in
claude-session-logs-formal-conjectures/91314939-d275-4bae... as a structured
extraction, plus sibling-corpus stubs — flagged; volume numbers and the
non-latex-page entries are unverified offline: DEFERRED where noted):
- [Cr03] Croot, III, Ernest S., _On a coloring conjecture about unit
  fractions_. Ann. of Math. (2) (2003), 545–556. (Journal, year, pages from
  the log-recovered /latex/46 extraction; the volume — **157** — appears only
  in the sibling corpus and reviewer knowledge, not in the extraction:
  DEFERRED.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980). This problem: p. 36. (From the /latex/46 extraction; the page-number
  qualifier from the site's citation line.)
- [Er77c] Erdős, P., _Problems and results on combinatorial number theory.
  III_. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43–72. (Stub: consistent sibling-corpus entry; unverified offline.)
- [Er96b] Erdős, P., _Some problems I presented or planned to present in my
  short talk_. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995)
  (1996), 333–335. (Stub: consistent sibling-corpus entry; unverified
  offline.)
- [Er97c] Erdős, P., _Some recent problems and results in graph theory_.
  Discrete Math. 164 (1997), 81–85. (Stub: dominant sibling-corpus entry;
  unverified offline.)
- [Er92c] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Matematiche (Catania) 47 (1992), 231–240. (Stub: majority
  sibling-corpus entry; a minority of corpus files expand [Er92c] differently
  (Hardy-Ramanujan J. 15): DEFERRED.)
- [Er95] — key only: the corpus's expansions for this key conflict (Resenhas
  1 (1995), 165–186 vs Congressus Numerantium 107 (1995)): DEFERRED.

Tags: number theory | unit fractions | ramsey theory. No prize; OEIS: N/A.
Additional thanks to: Euro Vidal Sampaio and Desmond Weisenberg.
Source: https://www.erdosproblems.com/46
-/
theorem erdos_problem_46 (α : Type*) [Finite α] (c : ℕ → α) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ n ∈ S, n ≥ 2) ∧
      (∃ color : α, ∀ n ∈ S, c n = color) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = 1 :=
  sorry

/--
Strengthening proved by Croot [Cr03], stated on the source page ("indeed, there
are infinitely many disjoint such monochromatic solutions") and formalized
upstream as `erdos_46.variants.infinitely_many_disjoint`: every finite
colouring admits an infinite family of pairwise disjoint monochromatic finite
sets of integers ≥ 2, each with reciprocal sum 1. (Pairwise disjointness plus
nonemptiness makes the ℕ-indexed family genuinely infinite. Each set may use
its own colour.)

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_46.variants.infinitely_many_disjoint
    (α : Type*) [Finite α] (c : ℕ → α) :
    ∃ S : ℕ → Finset ℕ,
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) ∧
      ∀ i, (S i).Nonempty ∧
        (∀ n ∈ S i, n ≥ 2) ∧
        (∃ color : α, ∀ n ∈ S i, c n = color) ∧
        (∑ n ∈ S i, (1 : ℚ) / (n : ℚ)) = 1 :=
  sorry

/--
Generalization asked in [ErGr80] and stated on the source page, formalized
upstream as `erdos_46.variants.positive_rat`: for every finite colouring and
every positive rational q, there is a monochromatic finite set of integers
≥ 2 whose reciprocals sum to q. Solved — the page derives it from the unit
case (via the infinitely-many-disjoint strengthening applied to the induced
colouring of {n/b : b ∣ n}).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_46.variants.positive_rational
    (α : Type*) [Finite α] (c : ℕ → α) (q : ℚ) (hq : 0 < q) :
    ∃ S : Finset ℕ, S.Nonempty ∧
      (∀ n ∈ S, n ≥ 2) ∧
      (∃ color : α, ∀ n ∈ S, c n = color) ∧
      (∑ n ∈ S, (1 : ℚ) / (n : ℚ)) = q :=
  sorry
