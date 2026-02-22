import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #789

Let h(n) be maximal such that if A ⊆ ℤ with |A| = n then there is B ⊆ A
with |B| ≥ h(n) such that if a₁ + ⋯ + aᵣ = b₁ + ⋯ + bₛ with aᵢ, bᵢ ∈ B
then r = s.

Estimate h(n).

Erdős [Er62c] proved h(n) ≪ n^{5/6}. Straus [St66] proved h(n) ≪ n^{1/2}.
Erdős noted h(n) ≫ n^{1/3}. Erdős [Er62c] and Choi [Ch74b] improved the
lower bound to h(n) ≫ (n log n)^{1/3}.

https://www.erdosproblems.com/789
-/

/-- A subset B of ℤ has the "sum-length property" if whenever
    a₁ + ⋯ + aᵣ = b₁ + ⋯ + bₛ with all aᵢ, bⱼ ∈ B, then r = s. -/
def SumLengthProperty (B : Finset ℤ) : Prop :=
  ∀ (as bs : List ℤ), (∀ a ∈ as, a ∈ B) → (∀ b ∈ bs, b ∈ B) →
    as.sum = bs.sum → as.length = bs.length

/-- h(n) is the maximal h such that every n-element subset A of ℤ contains a
    subset B of size ≥ h with the sum-length property. -/
noncomputable def erdos789_h (n : ℕ) : ℕ :=
  sSup { h : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ h ≤ B.card ∧ SumLengthProperty B }

/--
Erdős Problem #789, upper bound (Straus [St66]):

h(n) ≪ n^{1/2}, i.e., there exists C > 0 such that h(n) ≤ C · n^{1/2}
for all n.
-/
theorem erdos_problem_789_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ,
      (erdos789_h n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #789, lower bound (Erdős [Er62c] and Choi [Ch74b]):

h(n) ≫ (n log n)^{1/3}, i.e., there exist C > 0 and N₀ such that for all
n ≥ N₀, h(n) ≥ C · (n · log n)^{1/3}.
-/
theorem erdos_problem_789_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos789_h n : ℝ) ≥ C * ((n : ℝ) * Real.log (n : ℝ)) ^ ((1 : ℝ) / 3) :=
  sorry

end
