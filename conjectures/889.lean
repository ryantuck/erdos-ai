import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic

open Nat Finset

/--
For n ≥ 1 and k ≥ 0, v(n, k) counts the number of (distinct) prime factors
of n + k which are strictly greater than k. (Equivalently, the prime factors
of n + k that do not divide any of n, n+1, …, n+k-1.)
-/
def erdos889_v (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (· > k)).card

/--
v₀(n) = max over k ≥ 0 of v(n, k). Since v(n, k) = 0 for k ≥ n + k
(vacuously bounded), the supremum is realized and finite. We express it as:
for every bound M, eventually v₀(n) ≥ M.
-/
def erdos889_v0 (n : ℕ) : ℕ :=
  Finset.sup' (Finset.range (n + 1)) (Finset.nonempty_range_iff.mpr (by omega))
    (fun k => erdos889_v n k)

/--
Erdős Problem #889 [ErSe67, p.428] [Er98, p.178]:

For k ≥ 0 and n ≥ 1, let v(n, k) count the prime factors of n + k which are
strictly greater than k. Let v₀(n) = max_{k ≥ 0} v(n, k).

Is it true that v₀(n) → ∞ as n → ∞?

A question of Erdős and Selfridge, who could only show that v₀(n) ≥ 2 for
n ≥ 17. This is problem B27 of Guy's collection [Gu04].
-/
theorem erdos_problem_889 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      erdos889_v0 n ≥ M :=
  sorry
