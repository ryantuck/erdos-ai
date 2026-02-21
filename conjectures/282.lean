import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Lattice

/-!
# Erdős Problem #282

Let A ⊆ ℕ be an infinite set and consider the following greedy algorithm for
a rational x ∈ (0,1): choose the minimal n ∈ A such that n ≥ 1/x and repeat
with x replaced by x - 1/n. If this terminates after finitely many steps then
this produces a representation of x as the sum of distinct unit fractions with
denominators from A.

Does this process always terminate if x has odd denominator and A is the set
of odd numbers? The problem when A is the set of odd numbers is due to Stein.
In 1202, Fibonacci observed that the process terminates for any x when A = ℕ.
-/

/-- The greedy step: given a set A ⊆ ℕ and a positive rational x,
    returns the minimal n ∈ A such that n ≥ 1/x. Returns 0 if x ≤ 0. -/
noncomputable def greedyDenominator (A : Set ℕ) (x : ℚ) : ℕ :=
  if x ≤ 0 then 0
  else sInf {n : ℕ | n ∈ A ∧ x⁻¹ ≤ (n : ℚ)}

/-- The greedy remainder sequence: starting from x, repeatedly subtract 1/n
    where n is chosen greedily as the minimal element of A with n ≥ 1/x. -/
noncomputable def greedyRemainder (A : Set ℕ) (x : ℚ) : ℕ → ℚ
  | 0 => x
  | k + 1 =>
    let r := greedyRemainder A x k
    if r ≤ 0 then 0
    else r - 1 / ↑(greedyDenominator A r)

/--
Erdős Problem #282 [ErGr80, p.30]:

The greedy algorithm for Egyptian fractions with odd denominators always
terminates: for every rational x ∈ (0,1) with odd denominator, the process of
repeatedly choosing the minimal odd n ≥ 1/x and replacing x by x - 1/n
terminates after finitely many steps.
-/
theorem erdos_problem_282 :
    ∀ x : ℚ, 0 < x → x < 1 → x.den % 2 = 1 →
    ∃ k : ℕ, greedyRemainder {n : ℕ | n % 2 = 1} x k = 0 :=
  sorry
