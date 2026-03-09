import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat

/--
One step of the iteration: n ↦ φ(n) + 1.
-/
def phiStep (n : ℕ) : ℕ := n.totient + 1

/--
The k-th iterate of phiStep starting from n.
-/
def phiIter (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => phiStep (phiIter n k)

/--
Erdős Problem #409 [ErGr80, p.81]:

How many iterations of n ↦ φ(n) + 1 are needed before a prime is reached?
Can infinitely many n reach the same prime? What is the density of n which
reach any fixed prime?

A problem of Finucane. Let F(n) count the number of iterations of
n ↦ φ(n) + 1 before reaching a prime. Cambie notes that F(n) = o(n) is
trivial and F(n) = 1 infinitely often. The intended question is to find
good upper bounds for F(n).

Part (a): For every n ≥ 2 the iteration n ↦ φ(n) + 1 eventually reaches
a prime.
-/
theorem erdos_problem_409a (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : ℕ, (phiIter n k).Prime :=
  sorry

/-- Part (b): Infinitely many n reach the same prime under iteration. -/
theorem erdos_problem_409b :
    ∃ p : ℕ, p.Prime ∧
      Set.Infinite {n : ℕ | ∃ k : ℕ, phiIter n k = p} :=
  sorry
