import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Algebra.Order.Floor
import Mathlib.NumberTheory.Divisors

open Filter Finset

/-- The count of natural numbers n such that n + f(n) falls in the open real
    interval (x, x + F(x)). Since n ≤ n + f(n) < x + F(x) requires n < x + F(x),
    it suffices to search n in the range [0, x + ⌈F x⌉₊]. -/
noncomputable def shiftCount (f : ℕ → ℕ) (F : ℕ → ℝ) (x : ℕ) : ℕ :=
  ((Finset.range (x + ⌈F x⌉₊ + 1)).filter
    (fun n => (x : ℝ) < (n : ℝ) + (f n : ℝ) ∧
              (n : ℝ) + (f n : ℝ) < (x : ℝ) + F x)).card

/-- The natural density of a set A ⊆ ℕ is zero: the proportion of elements
    in {0, …, N−1} belonging to A tends to 0 as N → ∞. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop (nhds 0)

/-- f(n)/F(n) → 0 for almost all n in the natural-density sense:
    for every ε > 0, the set {n : f(n)/F(n) ≥ ε} has natural density zero. -/
def AlmostAllRatioVanishes (f : ℕ → ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasNaturalDensityZero {n : ℕ | ε ≤ (f n : ℝ) / F n}

/-- The Erdős–122 property of f: for any positive F with f(n)/F(n) → 0
    in natural density, the ratio #{n ∈ ℕ : n+f(n) ∈ (x, x+F(x))} / F(x)
    is unbounded as x → ∞ (equivalently, its limsup equals +∞). -/
def HasErdos122Property (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℝ, (∀ n, 0 < F n) → AlmostAllRatioVanishes f F →
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C < (shiftCount f F x : ℝ) / F x

/--
Erdős Problem #122 [Er97, Er97e, EPS97] — OPEN

For which number-theoretic functions f : ℕ → ℕ is it true that for any
positive function F : ℕ → ℝ satisfying f(n)/F(n) → 0 for almost all n
(in the natural density sense), there are infinitely many x for which

  #{n ∈ ℕ : n + f(n) ∈ (x, x + F(x))} / F(x) → ∞?

Erdős, Pomerance, and Sárközy [EPS97] proved that this holds when:
  • f(n) = τ(n) = number of divisors of n, and
  • f(n) = ω(n) = number of distinct prime divisors of n.

Erdős believed the property to be FALSE for:
  • f(n) = φ(n)  (Euler's totient function), and
  • f(n) = σ(n)  (sum of divisors).

The full characterization of which f satisfy HasErdos122Property remains open.
The theorem below records the two proved instances.
-/
theorem erdos_problem_122 :
    HasErdos122Property (fun n => (Nat.divisors n).card) ∧
    HasErdos122Property (fun n => (Nat.factors n).toFinset.card) :=
  sorry
