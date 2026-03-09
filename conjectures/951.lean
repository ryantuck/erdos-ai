import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

open BigOperators Classical

noncomputable section

/--
The "generalized integer" associated to a finitely supported tuple `f : ℕ →₀ ℕ`
and a sequence `a : ℕ → ℝ`: the product ∏ᵢ a(i)^{f(i)}.
-/
noncomputable def beurlingProduct (a : ℕ → ℝ) (f : ℕ →₀ ℕ) : ℝ :=
  f.prod (fun i k => a i ^ k)

/--
A sequence `a : ℕ → ℝ` is a **Beurling prime sequence** if:
1. It is strictly increasing: a(0) < a(1) < a(2) < ⋯
2. All values are > 1: a(i) > 1 for all i.
3. All distinct generalized integers (products ∏ a(i)^{k_i}) are at least 1 apart:
   |∏ a(i)^{k_i} − ∏ a(j)^{ℓ_j}| ≥ 1 for all distinct finitely supported tuples.
-/
def IsBeurlingPrimeSeq (a : ℕ → ℝ) : Prop :=
  StrictMono a ∧
  (∀ i, 1 < a i) ∧
  (∀ f g : ℕ →₀ ℕ, f ≠ g →
    |beurlingProduct a f - beurlingProduct a g| ≥ 1)

/--
The counting function: the number of indices i such that a(i) ≤ x.
-/
noncomputable def beurlingCount (a : ℕ → ℝ) (x : ℕ) : ℕ :=
  Nat.card { i : ℕ // a i ≤ (x : ℝ) }

/--
Erdős Problem #951 [Er77c, p.68]:

Let 1 < a₁ < a₂ < ⋯ be a sequence of real numbers such that
  |∏ᵢ aᵢ^{kᵢ} − ∏ⱼ aⱼ^{ℓⱼ}| ≥ 1
for every distinct pair of non-negative finitely supported integer tuples.
(Such a sequence is called a set of Beurling prime numbers.)

Is it true that #{aᵢ ≤ x} ≤ π(x) for all sufficiently large x?

The question was asked during Erdős's lecture at Queens College by a member
of the audience (perhaps S. Shapiro).
-/
theorem erdos_problem_951 (a : ℕ → ℝ) (ha : IsBeurlingPrimeSeq a) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      beurlingCount a x ≤ Nat.primeCounting x :=
  sorry

end
