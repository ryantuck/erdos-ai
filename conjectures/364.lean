import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdős Problem #364

Are there any triples of consecutive positive integers all of which are
powerful (i.e. if p ∣ n then p² ∣ n)?

Erdős [Er76d] believed the answer is no. The abc conjecture implies there
are only finitely many such triples. It is known that there are no such
triples with n < 10²².

It is trivial that there are no quadruples of consecutive powerful numbers
since one must be 2 (mod 4).

See also [137].
-/

/-- A positive natural number N is *powerful* if for every prime p dividing N,
    p² also divides N. -/
def IsPowerful (N : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ N → p ^ 2 ∣ N

/--
Erdős Problem #364 [Er76d, ErGr80]:

There is no positive integer n such that n, n+1, and n+2 are all powerful.
-/
theorem erdos364 :
    ¬ ∃ n : ℕ, 0 < n ∧ IsPowerful n ∧ IsPowerful (n + 1) ∧ IsPowerful (n + 2) :=
  sorry
