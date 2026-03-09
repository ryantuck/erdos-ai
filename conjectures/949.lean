import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.SetTheory.Cardinal.Continuum

open Set Cardinal
open scoped Pointwise

/--
The set S ⊆ ℝ is **sum-free**: there are no a, b, c ∈ S with a + b = c.
-/
def SumFree (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + b ≠ c

/--
Erdős Problem #949 [Er77c]:

Let S ⊂ ℝ be a set containing no solutions to a + b = c (i.e., S is sum-free).
Must there exist a set A ⊆ ℝ \ S of cardinality continuum such that A + A ⊆ ℝ \ S?

Erdős suggests that if the answer is no, one could consider the variant where S
is assumed to be Sidon. Dillies gives a positive proof for the Sidon variant,
found by AlphaProof.
-/
theorem erdos_problem_949
    (S : Set ℝ)
    (hS : SumFree S) :
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧ #A = 𝔠 ∧ A + A ⊆ Sᶜ :=
  sorry
