import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.AbsoluteValue.Basic

open BigOperators Finset

private noncomputable def signedHarmonicSum (δ : ℕ → ℤ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, (δ k : ℚ) / (k : ℚ)

/--
Erdős Problem #317, Part 1 [ErGr80, p.42]:

Is there some constant c > 0 such that for every n ≥ 1 there exists
δ_k ∈ {-1, 0, 1} for 1 ≤ k ≤ n with
  0 < |∑_{k=1}^{n} δ_k/k| < c/2^n?
-/
theorem erdos_problem_317a :
    ∃ c : ℚ, 0 < c ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ δ : ℕ → ℤ,
          (∀ k, 1 ≤ k → k ≤ n → Int.natAbs (δ k) ≤ 1) ∧
          signedHarmonicSum δ n ≠ 0 ∧
          (if signedHarmonicSum δ n ≥ 0
           then signedHarmonicSum δ n
           else -signedHarmonicSum δ n) < c / (2 : ℚ) ^ n :=
  sorry

/--
Erdős Problem #317, Part 2 [ErGr80, p.42]:

Is it true that for sufficiently large n, for any δ_k ∈ {-1, 0, 1},
  |∑_{k=1}^{n} δ_k/k| > 1/lcm(1,...,n)
whenever the left-hand side is not zero?

(The inequality ≥ is trivial since the sum, when nonzero, is a nonzero
integer multiple of 1/lcm(1,...,n). The conjecture asks for strict inequality.)
-/
theorem erdos_problem_317b :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ δ : ℕ → ℤ,
          (∀ k, 1 ≤ k → k ≤ n → Int.natAbs (δ k) ≤ 1) →
          signedHarmonicSum δ n ≠ 0 →
          (1 : ℚ) / ((Finset.Icc 1 n).lcm id : ℕ) <
            (if signedHarmonicSum δ n ≥ 0
             then signedHarmonicSum δ n
             else -signedHarmonicSum δ n) :=
  sorry
