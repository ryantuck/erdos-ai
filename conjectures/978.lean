import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #978

Let f ∈ ℤ[x] be an irreducible polynomial of degree k > 2 (and suppose that k ≠ 2^l
for any l ≥ 1) such that the leading coefficient of f is positive.

1. Does the set of integers n ≥ 1 for which f(n) is (k-1)-power-free have positive density?
2. If k > 3 then are there infinitely many n for which f(n) is (k-2)-power-free?
3. In particular, does n⁴ + 2 represent infinitely many squarefree numbers?

Hooley [Ho67] settled the first question. Heath-Brown [He06] proved the answer to
the second question is yes when k ≥ 10, and Browning [Br11] extended this to k ≥ 9.

https://www.erdosproblems.com/978
-/

open Polynomial

/-- A natural number m is k-power-free if no prime p has p^k ∣ m. -/
def IsKPowerFree (k : ℕ) (m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p ^ k ∣ m)

/--
Erdős Problem #978, Part 3 (most concrete special case):

There are infinitely many positive integers n such that n⁴ + 2 is squarefree.
-/
theorem erdos_problem_978_part3 :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ Squarefree (n ^ 4 + 2) :=
  sorry

/--
Erdős Problem #978, Part 1:

Let f ∈ ℤ[x] be an irreducible polynomial of degree k > 2 with positive leading
coefficient, and suppose k is not a power of 2. Then the set of positive integers
n for which |f(n)| is (k-1)-power-free has positive lower density.

Formalized as: there exist C > 0 and N₀ such that for all N ≥ N₀,
the number of n ∈ [1,N] with |f(n)| being (k-1)-power-free is at least C · N.
-/
theorem erdos_problem_978_part1
    (f : Polynomial ℤ)
    (k : ℕ)
    (hk : f.natDegree = k)
    (hk_gt : k > 2)
    (hk_not_pow2 : ∀ l : ℕ, l ≥ 1 → k ≠ 2 ^ l)
    (hirr : Irreducible f)
    (hlead : 0 < f.leadingCoeff) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      ∃ S : Finset ℕ, (∀ n ∈ S, 1 ≤ n ∧ n ≤ N ∧
        IsKPowerFree (k - 1) (f.eval (n : ℤ)).natAbs) ∧
        (S.card : ℝ) ≥ C * (N : ℝ) :=
  sorry

/--
Erdős Problem #978, Part 2:

Let f ∈ ℤ[x] be an irreducible polynomial of degree k > 3 with positive leading
coefficient, and suppose k is not a power of 2. Then there are infinitely many
positive integers n for which |f(n)| is (k-2)-power-free.
-/
theorem erdos_problem_978_part2
    (f : Polynomial ℤ)
    (k : ℕ)
    (hk : f.natDegree = k)
    (hk_gt : k > 3)
    (hk_not_pow2 : ∀ l : ℕ, l ≥ 1 → k ≠ 2 ^ l)
    (hirr : Irreducible f)
    (hlead : 0 < f.leadingCoeff) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      IsKPowerFree (k - 2) (f.eval (n : ℤ)).natAbs :=
  sorry
