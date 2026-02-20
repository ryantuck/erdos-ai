import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-- A group G satisfies the n-commuting property if every finite subset of size
    greater than n contains two distinct elements x ≠ y with xy = yx. -/
def HasNCommutingProperty (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (S : Finset G), n < S.card →
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x * y = y * x

/-- A group G can be covered by at most k Abelian subgroups: there exist k subgroups
    H₀, …, Hₖ₋₁ (possibly with repetition), each of which is abelian, whose union
    is all of G. -/
def CoveredByAbelianSubgroups (k : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (H : Fin k → Subgroup G),
    (∀ i, ∀ a b : G, a ∈ H i → b ∈ H i → a * b = b * a) ∧
    ∀ g : G, ∃ i, g ∈ H i

/-- h(n) is the least k such that every group (in Type, i.e. the small universe)
    satisfying the n-commuting property can be covered by at most k Abelian
    subgroups. -/
noncomputable def erdosH (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [Group G],
    HasNCommutingProperty n G → CoveredByAbelianSubgroups k G}

/--
Erdős Problem #117 [Er90, Er97f, Va99]:

Let h(n) be minimal such that any group G satisfying the property that every
subset of more than n elements contains distinct commuting elements x ≠ y
(xy = yx) can be covered by at most h(n) Abelian subgroups.

Estimate h(n) as well as possible.

Pyber [Py87] proved there exist constants c₂ > c₁ > 1 such that
  c₁^n < h(n) < c₂^n.
The lower bound c₁^n < h(n) was already known to Isaacs [Er97f].
The precise exponential growth rate of h(n) remains open.
-/
theorem erdos_problem_117 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∀ n : ℕ, 1 ≤ n →
      c₁ ^ n < (erdosH n : ℝ) ∧ (erdosH n : ℝ) < c₂ ^ n :=
  sorry
