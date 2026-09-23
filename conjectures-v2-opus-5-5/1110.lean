-- [AI-Generated]: Erdős Problem 1110 — second-pass formalization
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

*Source:* [erdosproblems.com/1110](https://www.erdosproblems.com/1110) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
22 January 2026, captured 2026-02-23). [ErLe96]

Let p > q ≥ 2 be two coprime integers. We call n *representable* if it is the sum of
integers of the form p^k q^l, none of which divide each other.

If {p,q} ≠ {2,3} then what can be said about the density of non-representable numbers?
Are there infinitely many coprime non-representable numbers?

Erdős and Lewin [ErLe96] proved that there are finitely many non-representable numbers
if and only if {p,q} = {2,3}.

For {2,3}, Erdős [Er92b] had made the "silly conjecture" that every integer is
representable. It has a simple inductive proof, which proves the stronger statement that
an even n has a representation with all summands even: if n = 2m, apply induction to m;
if n is odd, subtract the largest power of 3 that is ≤ n and apply induction to the (even)
remainder.

Yu and Chen [YuCh22] prove that the set of representable numbers has density zero whenever
q > 3, or q = 3 and p > 6, or q = 2 and p > 10. They also prove that there are infinitely
many coprime non-representable numbers if q > 3, or q = 3 and p ≠ 5, or q = 2 and
p ∉ {3, 5, 9}. For the second question the cases left open are therefore exactly
(p, q) ∈ {(5, 3), (5, 2), (9, 2)}.

Erdős and Lewin [ErLe96] also asked whether all large n can be written as a sum of
numbers 2^k 3^l, none dividing another, each larger than f(n) for some f(n) → ∞. Let f(n)
be the fastest growing such function. Yu and Chen [YuCh22] proved
n / (log n)^{log₂ 3} ≪ f(n) ≪ n / log n, and Yang and Zhao [YaZh25] improved the lower
bound to f(n) ≫ n / log n. (Not formalized: it needs logarithms and a maximal-least-part
function, which are not among this file's constructs.) The case of three powers is #123;
see also #845 for {p,q} = {2,3}, and #246 for the problem without the non-divisibility
condition.

"Coprime non-representable numbers" is read as non-representable n with gcd(n, pq) = 1.

Computation (review scratch script, n ≤ 3000). Every 1 ≤ n ≤ 3000 is representable for
(p, q) = (3, 2). For the three open pairs, the numbers of coprime non-representable
n ≤ 3000 are 498 for (5, 2), 1401 for (5, 3) and 766 for (9, 2), with the largest just
below 3000. This is consistent with "yes".

Tags: number theory. OEIS: "possible". The page records "Formalised statement? No" as of
capture.

## References

* [Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231–240.
* [ErLe96] Erdős, P. and Lewin, M., _d-complete sequences of integers_. Math. Comp. (1996),
  837–840.
* [YuCh22] Yu, W.-X. and Chen, Y.-G., _On a conjecture of Erdős and Lewin_. J. Number Theory
  (2022), 763–778.
* [YaZh25] Yang, Q.-H. and Zhao, L., _A conjecture of Yu and Chen related to the
  Erdős–Lewin theorem_. Acta Arith. (2025), 277–286.

(As extracted by the original pipeline's fetch of `erdosproblems.com/latex/1110`; volume
numbers are not in that extraction.)
-/

/-- A positive integer m is a (p,q)-power if m = p^a * q^b for some a, b ≥ 0. -/
def IsPQPower (p q m : ℕ) : Prop :=
  ∃ a b : ℕ, m = p ^ a * q ^ b

/-- A finite set of natural numbers is an antichain under divisibility:
    no element divides a distinct element. (Equivalent to Mathlib's
    `IsAntichain (· ∣ ·) (S : Set ℕ)`.) -/
def IsDivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

/-- A natural number n is (p,q)-representable if n equals the sum of a nonempty finite set
    of numbers of the form p^a * q^b, where no element divides another. (Distinctness of
    the summands is automatic, since equal summands would divide each other.) -/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧
    (∀ m ∈ S, IsPQPower p q m) ∧
    IsDivisibilityAntichain S ∧
    S.sum id = n

/--
Erdős Problem #1110 [ErLe96] (OPEN):

For coprime integers p > q ≥ 2 with {p,q} ≠ {2,3}, there are infinitely many
non-representable numbers that are coprime to p·q.

Since p > q ≥ 2 and p, q are coprime, the only excluded case is p = 3, q = 2.

This is the second question, stated in its asked ("yes") direction for all admissible
pairs. By [YuCh22] (`variants.yu_chen_coprime`) it is known except for
(p, q) ∈ {(5, 3), (5, 2), (9, 2)}.
-/
theorem erdos_problem_1110 :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      ¬(p = 3 ∧ q = 2) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} :=
  sorry

/-- Erdős–Lewin [ErLe96] (solved): the set of non-representable numbers is finite if and
only if {p, q} = {2, 3}, i.e. (p, q) = (3, 2) under the convention p > q. -/
theorem erdos_problem_1110.variants.erdos_lewin :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (Set.Finite {n : ℕ | ¬IsRepresentable p q n} ↔ (p = 3 ∧ q = 2)) :=
  sorry

/-- [Er92b] (solved; the simple inductive proof is recorded in the module docstring): for
{p, q} = {2, 3} every positive integer is representable. -/
theorem erdos_problem_1110.variants.two_three :
    ∀ n : ℕ, 0 < n → IsRepresentable 3 2 n :=
  sorry

/-- Yu–Chen [YuCh22] (solved): there are infinitely many coprime non-representable numbers
if q > 3, or q = 3 and p ≠ 5, or q = 2 and p ∉ {3, 5, 9}. -/
theorem erdos_problem_1110.variants.yu_chen_coprime :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (3 < q ∨ (q = 3 ∧ p ≠ 5) ∨ (q = 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 9)) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} :=
  sorry

/-- Yu–Chen [YuCh22] (solved): the representable numbers have density zero if q > 3, or
q = 3 and p > 6, or q = 2 and p > 10. Density zero is written without division: for every
k ≥ 1, eventually k · #{n ≤ N : n representable} ≤ N + 1. -/
theorem erdos_problem_1110.variants.yu_chen_density_zero :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (3 < q ∨ (q = 3 ∧ 6 < p) ∨ (q = 2 ∧ 10 < p)) →
      ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        k * ((Finset.range (N + 1)).filter (fun n => IsRepresentable p q n)).card ≤ N + 1 :=
  sorry

end Erdos1110

end
