import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/-!
# Erdős Problem #1056

Let $k \geq 2$. Does there exist a prime $p$ and consecutive intervals
$I_1, \ldots, I_k$ such that $\prod_{n \in I_i} n \equiv 1 \pmod{p}$
for all $1 \leq i \leq k$?

Erdős observed (1979) that $3 \cdot 4 \equiv 5 \cdot 6 \cdot 7 \equiv 1 \pmod{11}$,
establishing $k = 2$. Makowski found, for $k = 3$,
$2 \cdot 3 \cdot 4 \cdot 5 \equiv 6 \cdot 7 \cdot 8 \cdot 9 \cdot 10 \cdot 11
\equiv 12 \cdot 13 \cdot 14 \cdot 15 \equiv 1 \pmod{17}$.
-/

/--
Erdős Problem #1056 (OPEN):

For every k ≥ 2, there exist a prime p and breakpoints a(0) < a(1) < ⋯ < a(k)
defining consecutive intervals Iᵢ = [a(i-1), a(i) - 1] for 1 ≤ i ≤ k,
such that the product of elements in each interval is ≡ 1 (mod p).
-/
theorem erdos_problem_1056 (k : ℕ) (hk : 2 ≤ k) :
    ∃ (p : ℕ) (_ : Nat.Prime p) (a : Fin (k + 1) → ℕ),
      StrictMono a ∧
      ∀ i : Fin k,
        (Finset.Icc (a i.castSucc) (a i.succ - 1)).prod id % p = 1 :=
  sorry
