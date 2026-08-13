import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-!
# Erdős Problem #1056

Let $k \geq 2$. Does there exist a prime $p$ and consecutive intervals
$I_1, \ldots, I_k$ such that $\prod_{n \in I_i} n \equiv 1 \pmod{p}$
for all $1 \leq i \leq k$?

This is problem A15 in Guy's collection [Gu04], where he reports that in a
letter in 1979 Erdős observed that $3 \cdot 4 \equiv 5 \cdot 6 \cdot 7 \equiv 1
\pmod{11}$, establishing $k = 2$. Makowski [Ma83] found, for $k = 3$,
$2 \cdot 3 \cdot 4 \cdot 5 \equiv 6 \cdot 7 \cdot 8 \cdot 9 \cdot 10 \cdot 11
\equiv 12 \cdot 13 \cdot 14 \cdot 15 \equiv 1 \pmod{17}$.

Noll and Simmons asked, more generally, whether there are solutions to
$q_1! \equiv \cdots \equiv q_k! \pmod{p}$ for arbitrarily large $k$
(with $q_1 < \cdots < q_k$).

Status: OPEN ([erdosproblems.com/1056](https://www.erdosproblems.com/1056),
page last edited 29 September 2025). Related OEIS sequence: A060427.
An upstream formalization exists at google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1056.lean`.

References:

* [Gu04] Guy, R. K., *Unsolved Problems in Number Theory*, 3rd edition,
  Springer, 2004, Problem A15.
* [Ma83] Makowski (1983). Full bibliographic details were not recoverable
  offline (the site loads its bibliography separately); surname from the
  problem page's prose, year inferred from the citation key.
-/

/--
Erdős Problem #1056 (OPEN):

For every k ≥ 2, there exist a prime p and breakpoints a(0) < a(1) < ⋯ < a(k)
defining consecutive intervals Iᵢ = [a(i-1), a(i) - 1] for 1 ≤ i ≤ k,
such that the product of elements in each interval is ≡ 1 (mod p).

The source poses this as a yes/no question; this raw statement asserts the
affirmative direction, which is the conjectured one (known for k = 2, 3).
-/
theorem erdos_problem_1056 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (p : ℕ) (_ : Nat.Prime p) (a : Fin (k + 1) → ℕ),
      StrictMono a ∧
      ∀ i : Fin k,
        (Icc (a i.castSucc) (a i.succ - 1)).prod id % p = 1 :=
  sorry

/--
The case k = 2 (Erdős, in a 1979 letter, as reported in [Gu04]):
3·4 ≡ 5·6·7 ≡ 1 (mod 11). This witnesses `erdos_problem_1056` for k = 2
with p = 11 and breakpoints a = (3, 5, 8).
-/
theorem erdos_problem_1056_k2 :
    (Icc 3 4).prod id % 11 = 1 ∧ (Icc 5 7).prod id % 11 = 1 := by
  decide

/--
The case k = 3 (Makowski [Ma83]):
2·3·4·5 ≡ 6·7·8·9·10·11 ≡ 12·13·14·15 ≡ 1 (mod 17). This witnesses
`erdos_problem_1056` for k = 3 with p = 17 and breakpoints a = (2, 6, 12, 16).
-/
theorem erdos_problem_1056_k3 :
    (Icc 2 5).prod id % 17 = 1 ∧ (Icc 6 11).prod id % 17 = 1 ∧
      (Icc 12 15).prod id % 17 = 1 := by
  decide

/--
Noll and Simmons asked, more generally, whether there are solutions to
q₀! ≡ q₁! ≡ ⋯ ≡ q_k! (mod p) with q₀ < q₁ < ⋯ < q_k < p for arbitrarily
large k (OPEN; this raw statement asserts the affirmative direction).

The bound q_i < p is the implicit nontriviality requirement: without it, any
increasing q's with q₀ ≥ p give q_i! ≡ 0 (mod p) for all i. Since each q_i!
with q_i < p is invertible mod p, the chain of factorial congruences is
equivalent to each consecutive interval product ∏_{n ∈ [q_i + 1, q_{i+1}]} n
being ≡ 1 (mod p), which is the form stated here. Solutions for k restrict to
solutions for any smaller k, so "arbitrarily large k" is equivalent to
"for all k".
-/
theorem erdos_problem_1056_noll_simmons (k : ℕ) :
    ∃ (p : ℕ) (_ : Nat.Prime p) (q : Fin (k + 1) → ℕ),
      StrictMono q ∧ (∀ i, q i < p) ∧
      ∀ i : Fin k,
        (Icc (q i.castSucc + 1) (q i.succ)).prod id % p = 1 :=
  sorry
