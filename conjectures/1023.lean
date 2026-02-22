import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1023

Let F(n) be the maximal size of a family of subsets of {1,…,n} such that
no set in this family is the union of other members of the family. Is it
true that there is a constant c > 0 such that F(n) ~ c · 2^n / √n?

Erdős and Kleitman proved that F(n) ≍ 2^n / √n. Hunter observes that the
answer follows from the solution to problem [447], which implies
F(n) ~ C(n, n/2).
-/

/-- A family `𝓕` of subsets of `Fin n` is *union-free* if no member of `𝓕`
    equals the union of some non-empty sub-collection of other members. -/
def IsUnionFreeFamily {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ S ⊆ 𝓕.erase A, S.Nonempty → S.sup id ≠ A

/-- `unionFreeMax n` is the maximum cardinality of a union-free family of
    subsets of `Fin n`. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ 𝓕 : Finset (Finset (Fin n)), IsUnionFreeFamily 𝓕 ∧ 𝓕.card = k}

/--
Erdős Problem #1023 [Er71,p.105]:

There exists a constant c > 0 such that F(n) ~ c · 2^n / √n, where F(n)
is the maximum size of a union-free family of subsets of {1,…,n}.

Formulated as: lim_{n → ∞} F(n) · √n / (c · 2^n) = 1.
-/
theorem erdos_problem_1023 :
    ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n : ℕ => (unionFreeMax n : ℝ) * Real.sqrt (↑n) / (c * (2 : ℝ) ^ n))
      Filter.atTop (nhds 1) :=
  sorry

end
