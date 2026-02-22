import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.Divisors

open Finset Filter

/-- The number of divisors of k that lie strictly between n and m. -/
def countDivisorsInOpenInterval (k n m : ℕ) : ℕ :=
  ((Nat.divisors k).filter (fun d => n < d ∧ d < m)).card

/-- The proportion of positive integers up to N having exactly one divisor
    in the open interval (n, m). This approximates δ₁(n, m). -/
noncomputable def delta1Approx (n m N : ℕ) : ℝ :=
  (((Finset.range (N + 1)).filter
    (fun k => 0 < k ∧ countDivisorsInOpenInterval k n m = 1)).card : ℝ) / (N : ℝ)

/-- The natural density δ₁(n, m) exists and equals d:
    the limit of |{k ≤ N : k has exactly one divisor in (n, m)}| / N equals d. -/
def HasDelta1Density (n m : ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto (fun N => delta1Approx n m N) Filter.atTop (nhds d)

/--
Erdős Problem #692 [Er79e, Ob1] — DISPROVED

Let δ₁(n, m) be the natural density of the set of positive integers with exactly
one divisor in the open interval (n, m). Erdős asked (1986, Oberwolfach) whether,
for fixed n, δ₁(n, m) is unimodal as a function of m for m > n + 1.

Cambie [Ca25] disproved this by showing it fails even for n = 3:
  δ₁(3, 6) = 0.35,  δ₁(3, 7) ≈ 0.33,  δ₁(3, 8) ≈ 0.3619,
exhibiting a "valley" at m = 7 that contradicts unimodality.
Furthermore, for fixed n, the sequence δ₁(n, m) has superpolynomially many
local maxima in m.

The theorem formalizes the disproof: there exist n, m₁ < m₂ < m₃ (all > n + 1)
such that δ₁(n, m₂) < δ₁(n, m₁) and δ₁(n, m₂) < δ₁(n, m₃).
-/
theorem erdos_problem_692 :
    ∃ n m₁ m₂ m₃ : ℕ, n + 1 < m₁ ∧ m₁ < m₂ ∧ m₂ < m₃ ∧
      ∃ d₁ d₂ d₃ : ℝ,
        HasDelta1Density n m₁ d₁ ∧
        HasDelta1Density n m₂ d₂ ∧
        HasDelta1Density n m₃ d₃ ∧
        d₂ < d₁ ∧ d₂ < d₃ := sorry
