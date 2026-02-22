import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter Finset

noncomputable section

/-!
# Erdős Problem #1005

Let a₁/b₁, a₂/b₂, ... be the Farey fractions of order n ≥ 4. Let f(n) be
the largest integer such that for all pairs of indices k < l with l ≤ k + f(n),
the fractions a_k/b_k and a_l/b_l are "similarly ordered":
  (a_k - a_l)(b_k - b_l) ≥ 0.

Is there a constant c > 0 such that f(n)/n → c as n → ∞?

Erdős [Er43] proved f(n) ≫ n. van Doorn [vD25b] proved
  (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1),
and conjectures c = 1/4.
-/

/-- The Farey fractions of order n: all reduced fractions a/b ∈ [0,1] with
    b ≤ n, as a sorted list of rationals. -/
def fareyFractions (n : ℕ) : List ℚ :=
  ((Finset.Icc 1 n).biUnion fun b =>
    ((Finset.range (b + 1)).filter fun a => Nat.Coprime a b).image
      fun (a : ℕ) => (a : ℚ) / (b : ℚ)).sort (· ≤ ·)

/-- Two Farey fractions p = a₁/b₁ and q = a₂/b₂ (in lowest terms) are
    similarly ordered if (a₁ - a₂)(b₁ - b₂) ≥ 0. -/
def similarlyOrdered (p q : ℚ) : Prop :=
  (p.num - q.num) * ((p.den : ℤ) - q.den) ≥ 0

/-- f(n): the largest d such that for all pairs of indices i < j with j ≤ i + d
    in the Farey sequence of order n, the fractions are similarly ordered. -/
noncomputable def fareySimOrderFn (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∀ i j : ℕ, i < j → j ≤ i + d →
    ∀ (hi : i < (fareyFractions n).length) (hj : j < (fareyFractions n).length),
    similarlyOrdered ((fareyFractions n).get ⟨i, hi⟩) ((fareyFractions n).get ⟨j, hj⟩)}

/--
Erdős Problem #1005 [Er43]:

There exists a constant c > 0 such that f(n)/n → c as n → ∞, where f(n) is
the largest window size for similarly ordered consecutive Farey fractions of
order n.

van Doorn [vD25b] proved (1/12 - o(1))n ≤ f(n) ≤ n/4 + O(1) and conjectures
c = 1/4.
-/
theorem erdos_problem_1005 :
    ∃ c : ℝ, c > 0 ∧
    Tendsto (fun n : ℕ => (fareySimOrderFn n : ℝ) / (n : ℝ)) atTop (nhds c) :=
  sorry

end
