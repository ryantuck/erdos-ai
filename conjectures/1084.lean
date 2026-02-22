import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Defs

/-!
# Erdős Problem #1084

Let f_d(n) be minimal such that in any collection of n points in ℝ^d, all of
distance at least 1 apart, there are at most f_d(n) many pairs of points which
are distance 1 apart. Estimate f_d(n).

This is sometimes known as the contact number problem.

Known results:
- f_1(n) = n - 1
- f_2(n) = ⌊3n - √(12n - 3)⌋ for all n ≥ 2 (Harborth [Ha74b])
- There exist c₁, c₂ > 0 such that 6n - c₁n^{2/3} < f_3(n) < 6n - c₂n^{2/3}
- In general, (d - o(1))n ≤ f_d(n) ≤ 2^{O(d)} n

Tags: geometry | distances
-/

noncomputable section

/-- A finite set of points in ℝ^d is a (unit) packing if all distinct pairs
    have distance at least 1. -/
def IsUnitPacking {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → dist p q ≥ 1

/-- The number of ordered pairs of distinct points at unit distance in a
    point set. The number of unordered contact pairs is this divided by 2. -/
def orderedContactCount {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {pq : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) |
    pq.1 ∈ P ∧ pq.2 ∈ P ∧ pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1}

/-- The number of (unordered) contact pairs in a point set: pairs {p, q} with
    p ≠ q and dist p q = 1. -/
def contactPairCount {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  orderedContactCount P / 2

/-- f_d(n): the maximum number of contact pairs (unit-distance pairs) over all
    packings of n points in ℝ^d (the contact number). -/
def contactNumber (d : ℕ) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (P : Finset (EuclideanSpace ℝ (Fin d))),
    P.card = n ∧ IsUnitPacking P ∧ contactPairCount P = m}

/--
**Erdős Problem #1084** — dimension 1:

The contact number in ℝ¹ is f_1(n) = n - 1 for all n ≥ 1.
-/
theorem erdos_problem_1084_dim1 (n : ℕ) (hn : n ≥ 1) :
    contactNumber 1 n = n - 1 :=
  sorry

/--
**Erdős Problem #1084** — Harborth's theorem [Ha74b]:

For all n ≥ 2, the contact number in ℝ² satisfies
  f_2(n) = ⌊3n - √(12n - 3)⌋.
-/
theorem erdos_problem_1084_harborth (n : ℕ) (hn : n ≥ 2) :
    contactNumber 2 n = Nat.floor (3 * (n : ℝ) - Real.sqrt (12 * (n : ℝ) - 3)) :=
  sorry

/--
**Erdős Problem #1084** — 3-dimensional bounds [Er75f]:

There exist constants c₁, c₂ > 0 such that for all sufficiently large n,
  6n - c₁ · n^{2/3} < f_3(n) < 6n - c₂ · n^{2/3}.
-/
theorem erdos_problem_1084_dim3 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      6 * (n : ℝ) - c₁ * (n : ℝ) ^ ((2 : ℝ) / 3) < ↑(contactNumber 3 n) ∧
      ↑(contactNumber 3 n) < 6 * (n : ℝ) - c₂ * (n : ℝ) ^ ((2 : ℝ) / 3) :=
  sorry

end
