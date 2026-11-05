-- [AI - Claude Opus 5.5]: Erdős Problem 191 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Real BigOperators

/-!
# Erdős Problem #191

*Source:* [erdosproblems.com/191](https://www.erdosproblems.com/191) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 08 February 2026).
[ErGr79, p.333] [ErGr80, p.17] [Er81, p.15] [Er82e, p.78]

Let $C>0$ be arbitrary. Is it true that, if $n$ is sufficiently large depending on $C$, then in
any $2$-colouring of $\binom{\{2,\ldots,n\}}{2}$ there exists some $X\subseteq \{2,\ldots,n\}$
such that $\binom{X}{2}$ is monochromatic and $\sum_{x\in X}\frac{1}{\log x}\geq C$?

Remarks recorded on the page (abridged): the answer is yes, which was proved by Rödl [Ro03]. In
the same article Rödl constructed, for all $n$, a $2$-colouring in which every monochromatic $X$
has $\sum_{x\in X}1/\log x\ll\log\log\log n$, and proved that the answer is negative for
$3$-colourings. This bound is best possible: Conlon, Fox, and Sudakov [CFS13] proved that for large
$n$ every $2$-colouring has a monochromatic $X$ with $\sum_{x\in X}1/\log x\geq
2^{-8}\log\log\log n$.

## Encoding notes

* A 2-colouring of the pairs of $\{2,\dots,n\}$ is a graph on `ℕ` (only the pairs inside
  $\{2,\dots,n\}$ matter); a monochromatic set is a clique of `G` or of `Gᶜ`.
* Every 2-element set is monochromatic, so small `C` are trivial: `{2, 3}` already gives
  $1/\log2+1/\log3\approx2.35$ (`variants.small_C`, PROVED in Lean). The content is for large `C`.
* [CFS13]'s bound implies the main theorem (`variants.main_of_cfs`, PROVED in Lean), since
  $\log\log\log n\to\infty$.

## References

From the site's `/latex/191` bibliography:
* [CFS13] Conlon, David, Fox, Jacob and Sudakov, Benny, _Two extensions of Ramsey's theorem_.
  Duke Math. J. (2013), 2903–2927.
* [Ro03] Rödl, Vojtěch, _On homogeneous sets of positive integers_. J. Combin. Theory Ser. A
  (2003), 229–240.

Erdős's sources:
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42. (Site `/latex/111`.)
* [Er82e] Erdős, Paul, _Some of my favourite problems which recently have been solved_ (1982),
  59–79. (Site `/latex/71`.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/191.lean` (Opus 5.5 review, `opus-5-5-review/191.md`).
-/

/--
Erdős Problem #191 [ErGr79, ErGr80, Er81, Er82e]:
For any C > 0, if n is sufficiently large (depending on C), then in any
2-colouring of the pairs from {2, ..., n}, there exists a monochromatic
set X ⊆ {2, ..., n} with ∑ x ∈ X, 1 / log x ≥ C.

Proved by Rödl [Ro03]. (Status: PROVED; the true direction.)
-/
theorem erdos_problem_191_conjecture :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ∀ G : SimpleGraph ℕ,
          ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
            (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
            C ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) := by
  sorry

/-- Small `C` are trivial (PROVED in Lean): the pair `{2, 3}` is monochromatic in every colouring,
and $1/\log2+1/\log3\approx2.35$. -/
theorem erdos_problem_191.variants.small_C (C : ℝ) (hC : C ≤ 1 / Real.log 2 + 1 / Real.log 3) :
    ∀ n ≥ 3, ∀ G : SimpleGraph ℕ,
      ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
        (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
        C ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) := by
  intro n hn G
  refine ⟨{2, 3}, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_Icc]
    omega
  · rw [Finset.coe_insert, Finset.coe_singleton]
    by_cases h : G.Adj 2 3
    · exact Or.inl (isClique_pair.2 fun _ => h)
    · exact Or.inr (isClique_pair.2 fun hne => (compl_adj G 2 3).2 ⟨hne, h⟩)
  · rw [Finset.sum_pair (by norm_num)]
    push_cast
    exact hC

/-- The quantitative bound of Conlon, Fox and Sudakov [CFS13] (SOLVED; not proved here). -/
theorem erdos_problem_191.variants.cfs :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph ℕ,
      ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
        (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
        (2 : ℝ)⁻¹ ^ 8 * Real.log (Real.log (Real.log n)) ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) :=
  sorry

/-- Rödl's construction [Ro03] (SOLVED; not proved here): the bound of [CFS13] is sharp up to the
constant. -/
theorem erdos_problem_191.variants.rodl_upper :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∃ G : SimpleGraph ℕ,
      ∀ X : Finset ℕ, X ⊆ Finset.Icc 2 n →
        (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) →
        ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) ≤ c * Real.log (Real.log (Real.log n)) :=
  sorry

/-- Rödl [Ro03] (SOLVED; not proved here): for 3-colourings the answer is no. A colouring of pairs is
a symmetric `c : ℕ → ℕ → Fin 3`; `X` is monochromatic if all its pairs get one colour. -/
theorem erdos_problem_191.variants.three_colours :
    ∃ C : ℝ, ∀ n : ℕ, ∃ c : ℕ → ℕ → Fin 3, (∀ x y, c x y = c y x) ∧
      ∀ X : Finset ℕ, X ⊆ Finset.Icc 2 n →
        (∃ i : Fin 3, ∀ x ∈ X, ∀ y ∈ X, x ≠ y → c x y = i) →
        ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) < C :=
  sorry

/-- [CFS13]'s bound implies the main theorem (PROVED in Lean). -/
theorem erdos_problem_191.variants.main_of_cfs
    (h : ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph ℕ,
      ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
        (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
        (2 : ℝ)⁻¹ ^ 8 * Real.log (Real.log (Real.log n)) ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ)) :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ∀ G : SimpleGraph ℕ,
          ∃ X : Finset ℕ, X ⊆ Finset.Icc 2 n ∧
            (G.IsClique (X : Set ℕ) ∨ Gᶜ.IsClique (X : Set ℕ)) ∧
            C ≤ ∑ x ∈ X, (1 : ℝ) / Real.log (x : ℝ) := by
  intro C _
  have htend : Filter.Tendsto (fun n : ℕ => Real.log (Real.log (Real.log n))) Filter.atTop
      Filter.atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (h.and (htend.eventually_ge_atTop ((2 : ℝ) ^ 8 * C)))
  refine ⟨N, fun n hn G => ?_⟩
  obtain ⟨hX, hbig⟩ := hN n hn
  obtain ⟨X, hXs, hXc, hXsum⟩ := hX G
  refine ⟨X, hXs, hXc, le_trans ?_ hXsum⟩
  have h8 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ 8 := by positivity
  calc C = (2 : ℝ)⁻¹ ^ 8 * ((2 : ℝ) ^ 8 * C) := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ 8 * Real.log (Real.log (Real.log n)) :=
        mul_le_mul_of_nonneg_left hbig h8.le
