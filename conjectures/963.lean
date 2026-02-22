import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log

open Finset BigOperators

/--
A finset of real numbers is *dissociated* if all subset sums are distinct:
for any two subsets S and T of B, if ∑_{b ∈ S} b = ∑_{b ∈ T} b then S = T.
-/
def IsDissociated (B : Finset ℝ) : Prop :=
  ∀ S T, S ⊆ B → T ⊆ B → (∑ b ∈ S, b) = (∑ b ∈ T, b) → S = T

/--
Erdős Problem #963 [Er65]:

Let f(n) be the maximal k such that in any set A ⊂ ℝ of size n there is a
dissociated subset B ⊆ A of size |B| ≥ k (i.e., all subset sums of B are
distinct). Is it true that f(n) ≥ ⌊log₂ n⌋?

Equivalently: for every finite set A ⊂ ℝ of size n, there exists a dissociated
subset B ⊆ A with |B| ≥ ⌊log₂ n⌋.

Erdős noted that the greedy algorithm shows f(n) ≥ ⌊log₃ n⌋.
-/
theorem erdos_problem_963 (A : Finset ℝ) (hA : A.Nonempty) :
    ∃ B : Finset ℝ, B ⊆ A ∧ IsDissociated B ∧
      Nat.log 2 A.card ≤ B.card :=
  sorry
