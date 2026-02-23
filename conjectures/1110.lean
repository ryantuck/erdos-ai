import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Classical

noncomputable section

namespace Erdos1110

/-!
# Erdős Problem #1110

Let p > q ≥ 2 be two coprime integers. We call n *representable* if it is the sum of
integers of the form p^k q^l, none of which divide each other.

If {p,q} ≠ {2,3} then what can be said about the density of non-representable numbers?
Are there infinitely many coprime non-representable numbers?

Erdős and Lewin [ErLe96] proved that there are finitely many non-representable numbers
if and only if {p,q} = {2,3}.

Yu and Chen [YuCh22] proved that the set of representable numbers has density zero for
many cases, and that there are infinitely many coprime non-representable numbers for
most parameter choices. Some cases remain open.

Tags: number theory
-/

/-- A positive integer m is a (p,q)-power if m = p^a * q^b for some a, b ≥ 0. -/
def IsPQPower (p q m : ℕ) : Prop :=
  ∃ a b : ℕ, m = p ^ a * q ^ b

/-- A finite set of natural numbers is an antichain under divisibility:
    no element divides a distinct element. -/
def IsDivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

/-- A natural number n is (p,q)-representable if n equals the sum of a nonempty finite set
    of numbers of the form p^a * q^b, where no element divides another. -/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧
    (∀ m ∈ S, IsPQPower p q m) ∧
    IsDivisibilityAntichain S ∧
    S.sum id = n

/--
Erdős Problem #1110 [ErLe96]:

For coprime integers p > q ≥ 2 with {p,q} ≠ {2,3}, there are infinitely many
non-representable numbers that are coprime to p·q.

Since p > q ≥ 2 and p, q are coprime, the only excluded case is p = 3, q = 2.
-/
theorem erdos_problem_1110 :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      ¬(p = 3 ∧ q = 2) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} :=
  sorry

end Erdos1110

end
