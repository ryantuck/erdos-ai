import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Filter Real Polynomial Classical

noncomputable section

/--
The divisor function τ(n) = |{d : d ∣ n}|, i.e., the number of positive divisors of n.
-/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/--
The sum ∑_{n ≤ X} τ(f(n)) for a polynomial f ∈ ℤ[x], where we take
f(n) as a natural number (using natAbs since we assume f(n) ≥ 1 for large n).
-/
def divisorSumAlongPoly (f : ℤ[X]) (X : ℕ) : ℕ :=
  ∑ n ∈ Finset.range X, tau (f.eval (n : ℤ)).natAbs

/--
Erdős Problem #975 [Er65b]:

Let f ∈ ℤ[x] be an irreducible non-constant polynomial such that f(n) ≥ 1 for all
sufficiently large n ∈ ℕ. Does there exist a constant c = c(f) > 0 such that
  ∑_{n ≤ X} τ(f(n)) ~ c · X · log X,
where τ is the divisor function?

Van der Corput [Va39] proved the lower bound ∑_{n≤X} τ(f(n)) ≫_f X log X, and
Erdős [Er52b] proved the upper bound ∑_{n≤X} τ(f(n)) ≪_f X log X using elementary
methods. The asymptotic formula is known for irreducible quadratics (Hooley [Ho63]).
For example, ∑_{n≤x} τ(n²+1) = (3/π) x log x + O(x).
-/
theorem erdos_problem_975
    (f : ℤ[X])
    (hIrr : Irreducible f)
    (hDeg : 0 < f.natDegree)
    (hPos : ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 1 ≤ f.eval (n : ℤ)) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun X : ℕ =>
        (divisorSumAlongPoly f X : ℝ) / (c * (X : ℝ) * log (X : ℝ)))
        atTop (nhds 1) :=
  sorry

end
