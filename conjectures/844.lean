import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Defs

open Classical

noncomputable section

/-!
# Erdős Problem #844

Let $A\subseteq \{1,\ldots,N\}$ be such that, for all $a,b\in A$, the product
$ab$ is not squarefree. Is the maximum size of such an $A$ achieved by taking
$A$ to be the set of even numbers and odd non-squarefree numbers?

A problem of Erdős and Sárközy [Er92b]. Proved affirmatively by Weisenberg,
and independently by Alexeev, Mixon, and Sawin [AMS25].

Tags: number theory, intersecting family
-/

/-- The candidate extremal set for Erdős Problem #844: all numbers in
    {1, …, N} that are either even or not squarefree. -/
noncomputable def erdos844_extremal (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => Even n ∨ ¬Squarefree n)

/--
**Erdős Problem #844** [Er92b]:

Let A ⊆ {1, …, N} be such that for all a, b ∈ A, the product ab is not
squarefree. Then |A| ≤ |erdos844_extremal N|.

Equivalently, the maximum is achieved by the set of all even numbers together
with all odd non-squarefree numbers in {1, …, N}.

Proved by Weisenberg, and independently by Alexeev, Mixon, and Sawin [AMS25].
-/
theorem erdos_problem_844 (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_prod : ∀ a ∈ A, ∀ b ∈ A, ¬Squarefree (a * b)) :
    A.card ≤ (erdos844_extremal N).card :=
  sorry

end
