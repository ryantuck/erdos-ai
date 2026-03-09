import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
Erdős Problem #354 [ErGr80,p.58]:

Let α, β ∈ ℝ₊ with α/β irrational. Is the multiset
  { ⌊α⌋, ⌊2α⌋, ⌊4α⌋, … } ∪ { ⌊β⌋, ⌊2β⌋, ⌊4β⌋, … }
complete? That is, can all sufficiently large natural numbers n be written as
  n = ∑_{s ∈ S} ⌊2^s α⌋ + ∑_{t ∈ T} ⌊2^t β⌋
for some finite S, T ⊆ ℕ?

This question was first mentioned by Graham. Hegyvári proved it holds when
α = m/2^n is a dyadic rational and β is not.
-/
theorem erdos_problem_354
    (α β : ℝ)
    (hα : 0 < α)
    (hβ : 0 < β)
    (hirr : Irrational (α / β)) :
    ∃ M : ℤ, ∀ n : ℤ, M ≤ n →
      ∃ (S T : Finset ℕ),
        (n : ℤ) = (∑ s ∈ S, ⌊(2 : ℝ) ^ (s : ℕ) * α⌋) +
                   (∑ t ∈ T, ⌊(2 : ℝ) ^ (t : ℕ) * β⌋) :=
  sorry
