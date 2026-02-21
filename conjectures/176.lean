import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #176

Let N(k, ℓ) be the minimal N such that for any f : {1,...,N} → {-1,1},
there must exist a k-term arithmetic progression P such that
|∑_{n ∈ P} f(n)| ≥ ℓ.

Is it true that for any c > 0 there exists some C > 1 such that
N(k, ck) ≤ Cᵏ? What about N(k, 2) ≤ Cᵏ or N(k, √k) ≤ Cᵏ?

When ℓ = k, N(k, k) is the van der Waerden number W(k).
-/

/-- The arithmetic progression discrepancy number N(k, ℓ): the minimal N such
    that for every f : {1,...,N} → {-1,1}, there exists a k-term arithmetic
    progression a, a+d, ..., a+(k-1)d with d ≥ 1 and all terms in {1,...,N}
    such that |∑ᵢ f(a + id)| ≥ ℓ. -/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ :=
  sInf { N : ℕ | ∀ f : ℕ → ℤ,
    (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
    ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
      ℓ ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| }

/--
Erdős Conjecture (Problem #176a) [Er65b, Er73, ErGr80]:
For any c > 0, there exists some C > 1 such that N(k, ck) ≤ Cᵏ.
-/
theorem erdos_problem_176a :
    ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (c * ↑k) : ℝ) ≤ C ^ k :=
  sorry

/--
Erdős Conjecture (Problem #176b) [Er65b, Er73, ErGr80]:
There exists some C > 1 such that N(k, 2) ≤ Cᵏ.
-/
theorem erdos_problem_176b :
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k 2 : ℝ) ≤ C ^ k :=
  sorry

/--
Erdős Conjecture (Problem #176c) [Er65b, Er73, ErGr80]:
There exists some C > 1 such that N(k, √k) ≤ Cᵏ.
-/
theorem erdos_problem_176c :
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (Real.sqrt ↑k) : ℝ) ≤ C ^ k :=
  sorry

end
