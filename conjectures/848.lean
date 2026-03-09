import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Defs

open Classical

noncomputable section

/-!
# Erdős Problem #848

Is the maximum size of a set $A\subseteq \{1,\ldots,N\}$ such that $ab+1$ is
never squarefree (for all $a,b\in A$) achieved by taking those
$n\equiv 7\pmod{25}$?

A problem of Erdős and Sárközy [Er92b]. Solved for all sufficiently large $N$
by Sawhney.

Tags: number theory
-/

/-- The candidate extremal set for Erdős Problem #848: all numbers in
    {1, …, N} that are congruent to 7 mod 25. -/
noncomputable def erdos848_extremal (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => n % 25 = 7)

/--
**Erdős Problem #848** [Er92b, p.239]:

Let A ⊆ {1, …, N} be such that for all a, b ∈ A, the integer ab + 1 is not
squarefree. Then |A| ≤ |erdos848_extremal N|.

Equivalently, the maximum is achieved by the set {n ∈ {1,…,N} : n ≡ 7 (mod 25)}.

Note: if a ≡ b ≡ 7 (mod 25), then ab + 1 ≡ 49 + 1 ≡ 50 ≡ 0 (mod 25),
so ab + 1 is divisible by 5² and hence not squarefree.

Solved for sufficiently large N by Sawhney.
-/
theorem erdos_problem_848 (N : ℕ) (A : Finset ℕ)
    (hA_sub : A ⊆ Finset.Icc 1 N)
    (hA_prod : ∀ a ∈ A, ∀ b ∈ A, ¬Squarefree (a * b + 1)) :
    A.card ≤ (erdos848_extremal N).card :=
  sorry

end
