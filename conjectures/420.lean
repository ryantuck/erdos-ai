import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Order.Floor.Defs

open Filter Topology Real

noncomputable section

/-!
# Erdős Problem #420

If τ(n) counts the number of divisors of n, define
  F(f, n) = τ((n + ⌊f(n)⌋)!) / τ(n!)

Three questions:
1. Is it true that lim_{n→∞} F((log n)^C, n) = ∞ for all sufficiently large C?
2. Is it true that F(log n, n) is everywhere dense in (1, ∞)?
3. More generally, if f(n) ≤ log n is a monotonic function with f(n) → ∞,
   then is F(f, n) everywhere dense in (1, ∞)?

Erdős and Graham note it is easy to show lim F(n^{1/2}, n) = ∞.
Erdős–Graham–Ivić–Pomerance [EGIP96] proved:
  • liminf F(c log n, n) = 1 for any c > 0
  • lim F(n^{4/9}, n) = ∞
  • if f(n) = o((log n)²), then F(f,n) ~ 1 for almost all n.
-/

/-- The ratio F(f, n) = τ((n + ⌊f(n)⌋)!) / τ(n!) where τ counts divisors.
    Here f : ℕ → ℝ and ⌊f(n)⌋₊ is the natural number floor of f(n). -/
noncomputable def erdos420_F (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((Nat.divisors (n + ⌊f n⌋₊).factorial).card : ℝ) /
  ((Nat.divisors n.factorial).card : ℝ)

/--
Erdős Problem #420 (Part 1) [ErGr80, p.83]:

Is it true that lim_{n→∞} F((log n)^C, n) = ∞ for all sufficiently large C?
-/
theorem erdos_problem_420_part1 :
    ∃ C₀ : ℝ, ∀ C : ℝ, C ≥ C₀ →
      Tendsto (fun n : ℕ => erdos420_F (fun m => (log (m : ℝ)) ^ C) n)
        atTop atTop :=
  sorry

/--
Erdős Problem #420 (Part 2) [ErGr80, p.83]:

Is it true that F(log n, n) is everywhere dense in (1, ∞)?
That is, for any 1 < a < b, there are infinitely many n with
a < F(log n, n) < b.
-/
theorem erdos_problem_420_part2 :
    ∀ a b : ℝ, 1 < a → a < b →
      ∃ᶠ n in atTop,
        a < erdos420_F (fun m => log (m : ℝ)) n ∧
        erdos420_F (fun m => log (m : ℝ)) n < b :=
  sorry

/--
Erdős Problem #420 (Part 3) [ErGr80, p.83]:

More generally, if f(n) ≤ log n is a monotonic function such that f(n) → ∞
as n → ∞, then is F(f, n) everywhere dense in (1, ∞)?
-/
theorem erdos_problem_420_part3 :
    ∀ f : ℕ → ℝ, Monotone f →
      (∀ n : ℕ, f n ≤ log (n : ℝ)) →
      Tendsto f atTop atTop →
      ∀ a b : ℝ, 1 < a → a < b →
        ∃ᶠ n in atTop,
          a < erdos420_F f n ∧ erdos420_F f n < b :=
  sorry

end
