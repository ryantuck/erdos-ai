import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #366

Are there any 2-full n such that n+1 is 3-full? That is, if p∣n then p²∣n and
if p∣(n+1) then p³∣(n+1).

Note that 8 is 3-full and 9 is 2-full. Erdős and Graham asked whether (8,9) is
the only such pair of consecutive integers. Stephan observed that 12167 = 23³
and 12168 = 2³·3²·13² is another example. By OEIS A060355 there are no other
examples for n < 10²².
-/

/-- A natural number N is *k-full* if for every prime p dividing N, p^k also divides N. -/
def IsKFull (k : ℕ) (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ k ∣ N

/--
Erdős Problem #366 [Er76d, ErGr80 p.68]:

There exists a positive integer n ≥ 1 such that n is 2-full and n+1 is 3-full.
-/
theorem erdos366 :
    ∃ n : ℕ, 1 ≤ n ∧ IsKFull 2 n ∧ IsKFull 3 (n + 1) :=
  sorry
