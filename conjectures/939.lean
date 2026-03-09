import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/-- A positive integer n is r-powerful if for every prime p dividing n,
    p^r also divides n. -/
def IsRPowerful (r : ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ r ∣ n

/--
Erdős Problem #939 [Er76d]:

Let r ≥ 2. An r-powerful number n is one such that if p ∣ n then p^r ∣ n.

If r ≥ 4 then can the sum of r-2 coprime r-powerful numbers ever be itself
r-powerful? Are there at most finitely many such solutions?

Cambie has found examples for r = 5, 7, and 8, so the first question is
answered positively. The finiteness question remains open.

The third part of the original problem (are there infinitely many triples of
coprime 3-powerful a, b, c with a+b=c?) was answered positively by Nitaj [Ni95].
-/
theorem erdos_problem_939 (r : ℕ) (hr : r ≥ 4) :
    Set.Finite {f : Fin (r - 2) → ℕ |
      (∀ i, IsRPowerful r (f i)) ∧
      (∀ i j : Fin (r - 2), i ≠ j → Nat.Coprime (f i) (f j)) ∧
      IsRPowerful r (∑ i : Fin (r - 2), f i)} :=
  sorry
