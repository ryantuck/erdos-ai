import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

/-- The reciprocal sum of a multiset of positive integers:
    ∑_{n ∈ A} 1/n, computed over ℝ. -/
def reciprocalSum (A : Multiset ℕ) : ℝ :=
  (A.map (fun n => (1 : ℝ) / ((n : ℕ) : ℝ))).sum

/--
Erdős Problem #312 [ErGr80]:

Does there exist some c > 0 such that, for any K > 1, whenever A is a
sufficiently large finite multiset of positive integers with
∑_{n ∈ A} 1/n > K, there exists some S ⊆ A (as a submultiset) such that
  1 - e^{-cK} < ∑_{n ∈ S} 1/n ≤ 1?

Erdős and Graham knew this with e^{-cK} replaced by c/K².
-/
theorem erdos_problem_312 :
    ∃ c : ℝ, 0 < c ∧
      ∀ K : ℝ, 1 < K →
        ∃ N₀ : ℕ, ∀ (A : Multiset ℕ),
          (∀ n ∈ A, 0 < n) →
          N₀ ≤ Multiset.card A →
          K < reciprocalSum A →
            ∃ S : Multiset ℕ, S ≤ A ∧
              1 - Real.exp (-c * K) < reciprocalSum S ∧
              reciprocalSum S ≤ 1 :=
  sorry

end
