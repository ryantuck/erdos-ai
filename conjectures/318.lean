import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A set A ⊆ ℕ has the **signed reciprocal zero-sum property** if for every
function f : A → {-1, 1} that is non-constant, there exists a finite
non-empty subset S ⊆ A such that ∑_{n ∈ S} f(n)/n = 0.
-/
def SignedReciprocalZeroSum (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℤ,
    (∀ n, n ∈ A → f n = 1 ∨ f n = -1) →
    (∃ a ∈ A, f a = 1) →
    (∃ b ∈ A, f b = -1) →
    ∃ S : Finset ℕ, S.Nonempty ∧ (↑S : Set ℕ) ⊆ A ∧
      ∑ n ∈ S, (f n : ℝ) / (n : ℝ) = 0

/--
Erdős Problem #318 [ErGr80,p.42]:

Let A ⊆ ℕ be the set of squares excluding 1, i.e., A = {4, 9, 16, 25, …}.
Let f : A → {-1, 1} be a non-constant function. Must there exist a finite
non-empty S ⊂ A such that ∑_{n ∈ S} f(n)/n = 0?

The original problem asked this for arbitrary infinite arithmetic progressions,
which was proved by Sattler [Sa82b]. The question for squares excluding 1
remains open. (For the squares including 1, the answer is trivially no since
∑_{k ≥ 2} 1/k² < 1.)
-/
theorem erdos_problem_318 :
    SignedReciprocalZeroSum {n : ℕ | ∃ k : ℕ, 2 ≤ k ∧ n = k ^ 2} :=
  sorry
