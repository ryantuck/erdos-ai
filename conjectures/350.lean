import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A finite set A of natural numbers is **dissociated** (has distinct subset sums)
if for any two subsets S₁, S₂ ⊆ A, equality of their sums implies S₁ = S₂.
-/
def Dissociated (A : Finset ℕ) : Prop :=
  ∀ S₁ ∈ A.powerset, ∀ S₂ ∈ A.powerset,
    S₁.sum id = S₂.sum id → S₁ = S₂

/--
Erdős Problem #350 [Er75b, Er77c, ErGr80,p.60]:

If A ⊂ ℕ is a finite set of positive integers which is dissociated (all subset
sums are distinct) then ∑_{n ∈ A} 1/n < 2.

This was proved by Ryavec (reproduced in [BeEr74]). More generally, Ryavec
showed ∑_{n ∈ A} 1/n ≤ 2 − 2^{1−|A|}, with equality iff A = {1, 2, …, 2^k}.
-/
theorem erdos_problem_350
    (A : Finset ℕ)
    (hA_pos : ∀ a ∈ A, 0 < a)
    (hA_diss : Dissociated A) :
    ∑ n ∈ A, (1 : ℝ) / (n : ℝ) < 2 :=
  sorry
