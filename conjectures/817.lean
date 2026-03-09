import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
The subset sums of a finite set A ⊆ ℕ:
  ⟨A⟩ = { ∑_{a ∈ S} a : S ⊆ A } = { ∑_{a ∈ A} εₐ a : εₐ ∈ {0,1} }.
-/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  A.powerset.image (fun S => S.sum id)

/--
A set S ⊆ ℕ contains a non-trivial k-term arithmetic progression:
there exist a, d with d ≥ 1 such that a, a+d, …, a+(k−1)d all lie in S.
-/
def ContainsAPInFinset (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ S

/--
Erdős Problem #817 [Er91]:

Let k ≥ 3 and define g_k(n) to be the minimal N such that {1,…,N}
contains some A of size |A| = n such that the subset sums
  ⟨A⟩ = { ∑_{a ∈ A} εₐ a : εₐ ∈ {0,1} }
contain no non-trivial k-term arithmetic progression.

Erdős and Sárközy proved g₃(n) ≫ 3ⁿ / n^{O(1)}.
The conjecture asks: is it true that g₃(n) ≫ 3ⁿ?

We formalize the specific question for k = 3: there exists C > 0
such that for all n, if A ⊆ {1,…,N} with |A| = n and ⟨A⟩ is free
of non-trivial 3-term APs, then N ≥ C · 3ⁿ.
-/
theorem erdos_problem_817 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N n : ℕ) (A : Finset ℕ),
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        A.card = n →
        ¬ ContainsAPInFinset (subsetSums A) 3 →
        (N : ℝ) ≥ C * 3 ^ n :=
  sorry
