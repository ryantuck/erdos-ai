import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #673

Let 1 = d₁ < ⋯ < d_{τ(n)} = n be the divisors of n and
  G(n) = Σ_{1 ≤ i < τ(n)} d_i / d_{i+1}.

Is it true that G(n) → ∞ for almost all n? Can one prove an asymptotic
formula for Σ_{n ≤ X} G(n)?

Erdős writes it is 'easy' to prove (1/X) Σ_{n ≤ X} G(n) → ∞.

Terence Tao observed that for any divisor m ∣ n,
  τ(n/m) / m ≤ G(n) ≤ τ(n),
and hence for example τ(n)/4 ≤ G(n) ≤ τ(n) for even n. It follows easily
that G(n) grows on average and tends to infinity for almost all n.

Erdős and Tenenbaum proved that G(n)/τ(n) has a continuous distribution
function.
-/

/-- The sorted list of divisors of n in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- G(n) = Σ_{1 ≤ i < τ(n)} d_i / d_{i+1}, where d₁ < ⋯ < d_{τ(n)} are the
    divisors of n in increasing order. This is the sum of ratios of consecutive
    divisors. -/
noncomputable def erdosG (n : ℕ) : ℝ :=
  let divs := sortedDivisors n
  ((divs.zip divs.tail).map (fun p => (p.1 : ℝ) / (p.2 : ℝ))).sum

/-- The natural density of a set A ⊆ ℕ is zero. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Tendsto
    (fun N : ℕ => (((Finset.range N).filter (· ∈ A)).card : ℝ) / (N : ℝ))
    atTop (nhds 0)

/--
Erdős Problem #673, Part 1 [Er79e, Er82e]:

G(n) → ∞ for almost all n, i.e., for every M, the set of n with G(n) ≤ M
has natural density zero.
-/
theorem erdos_problem_673_almost_all :
    ∀ M : ℝ, HasNaturalDensityZero {n : ℕ | erdosG n ≤ M} :=
  sorry

/--
Erdős Problem #673, Part 2 [Er79e, Er82e]:

(1/X) · Σ_{n ≤ X} G(n) → ∞ as X → ∞.
-/
theorem erdos_problem_673_average :
    Tendsto
      (fun X : ℕ => (Finset.sum (Finset.range X) erdosG) / (X : ℝ))
      atTop atTop :=
  sorry

end
