import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #700

Let f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)).

A problem of Erdős and Szekeres [ErSz78]:

1. Characterise those composite n such that f(n) = n/P(n), where P(n) is the
   largest prime dividing n.
2. Are there infinitely many composite n such that f(n) > n^{1/2}?
3. Is it true that, for every composite n, f(n) ≪_A n/(log n)^A for every A > 0?

It is easy to see that f(n) ≤ n/P(n) for composite n, and that f(n) ≥ p(n)
(the smallest prime factor). Hence f(n) ≥ n^{1/2} when n = p², and
f(n) ≤ (1+o(1)) n / log n in general. It is known that f(n) = n/P(n) when n
is a product of two primes, or n = 30.

https://www.erdosproblems.com/700
-/

/-- f(n) = min_{1 < k ≤ n/2} gcd(n, C(n,k)) for n ≥ 4; defined as 0 for n < 4. -/
def erdos700_f (n : ℕ) : ℕ :=
  if h : 4 ≤ n then
    ((Finset.Icc 2 (n / 2)).image (fun k => Nat.gcd n (Nat.choose n k))).min' (by
      exact ⟨Nat.gcd n (Nat.choose n 2), Finset.mem_image.mpr
        ⟨2, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩, rfl⟩⟩)
  else 0

/-- The largest prime factor of n. Returns 0 if n ≤ 1. -/
def greatestPrimeFactor (n : ℕ) : ℕ := n.primeFactorsList.foldl max 0

/--
Erdős Problem #700, Part (a) [ErSz78]:

For any composite n ≥ 4, f(n) ≤ n / P(n) where P(n) is the largest prime factor.
The characterization of those n where equality holds is the open question.
-/
theorem erdos_problem_700a (n : ℕ) (hn : 4 ≤ n) (hcomp : ¬ Nat.Prime n) :
    erdos700_f n ≤ n / greatestPrimeFactor n :=
  sorry

/--
Erdős Problem #700, Part (b) [ErSz78]:

There are infinitely many composite n such that f(n) > √n.
Here f(n) > √n is stated as f(n)² > n to remain in ℕ.
-/
theorem erdos_problem_700b :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ¬ Nat.Prime n ∧ 2 ≤ n ∧ (erdos700_f n) ^ 2 > n :=
  sorry

/--
Erdős Problem #700, Part (c) [ErSz78]:

For every composite n, f(n) ≪_A n / (log n)^A for every A > 0.

Formalized as: for every positive integer A, there exist C > 0 and N₀ such that
for all composite n ≥ N₀, f(n) ≤ C · n / (log n)^A. Using ℕ for A suffices
since the bound for integer A implies the bound for all real A' ≤ A.
-/
theorem erdos_problem_700c :
    ∀ A : ℕ, 0 < A →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ¬ Nat.Prime n → 2 ≤ n →
      (erdos700_f n : ℝ) ≤ C * (n : ℝ) / (Real.log (n : ℝ)) ^ A :=
  sorry

end
