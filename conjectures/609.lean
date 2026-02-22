import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical

noncomputable section

/-!
# Erdős Problem #609

Let f(n) be the minimal m such that if the edges of K_{2^n+1} are coloured
with n colours then there must be a monochromatic odd cycle of length at most m.
Estimate f(n).

A problem of Erdős and Graham [ErGr75]. The edges of K_{2^n} can be
n-coloured to avoid monochromatic odd cycles entirely (partition vertices by
binary coordinates). Day and Johnson [DaJo17] proved f(n) → ∞ and
f(n) ≥ 2^{c√(log n)} for some c > 0. Janzer and Yip [JaYi25] proved
f(n) ≤ O(n^{3/2} · 2^{n/2}).

Tags: graph theory | ramsey theory
-/

/-- There exists a monochromatic cycle of length `k` in an edge coloring of K_N.
    A cycle is an injective sequence of k ≥ 3 vertices v₀, …, v_{k-1} where all
    consecutive edges v₀v₁, v₁v₂, …, v_{k-1}v₀ have the same color. -/
def HasMonoCycle609 {N c : ℕ} (χ : Fin N → Fin N → Fin c) (k : ℕ) : Prop :=
  k ≥ 3 ∧
  ∃ (v : Fin k → Fin N),
    Function.Injective v ∧
    ∃ col : Fin c, ∀ i : Fin k,
      χ (v i) (v ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩) = col

/--
**Erdős Problem #609** [ErGr75]:

For every n ≥ 1, every symmetric n-coloring of the edges of K_{2^n+1}
contains a monochromatic odd cycle. (This establishes that f(n) is finite.)
-/
theorem erdos_problem_609_exists :
    ∀ n : ℕ, n ≥ 1 →
    ∀ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
      (∀ u v, χ u v = χ v u) →
      ∃ k, Odd k ∧ HasMonoCycle609 χ k :=
  sorry

/--
**Erdős Problem #609** (Day-Johnson lower bound) [DaJo17]:

There exists c > 0 such that for all sufficiently large n, there exists a
symmetric n-coloring of K_{2^n+1} with no monochromatic odd cycle of length
less than 2^{c·√(log n)}.
-/
theorem erdos_problem_609_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∃ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
        (∀ u v, χ u v = χ v u) ∧
        ∀ k, Odd k → HasMonoCycle609 χ k →
          (k : ℝ) ≥ (2 : ℝ) ^ (c * Real.sqrt (Real.log (n : ℝ))) :=
  sorry

/--
**Erdős Problem #609** (Janzer-Yip upper bound) [JaYi25]:

There exists C > 0 such that for all sufficiently large n, every symmetric
n-coloring of K_{2^n+1} contains a monochromatic odd cycle of length at most
C · n^{3/2} · 2^{n/2}.
-/
theorem erdos_problem_609_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ χ : Fin (2^n + 1) → Fin (2^n + 1) → Fin n,
        (∀ u v, χ u v = χ v u) →
        ∃ k, Odd k ∧ HasMonoCycle609 χ k ∧
          (k : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ ((n : ℝ) / 2) :=
  sorry

end
