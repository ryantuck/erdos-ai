import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #769

Let c(n) be minimal such that if k ≥ c(n) then the n-dimensional unit cube
can be decomposed into k homothetic n-dimensional cubes. Is it true that
c(n) ≫ n^n?

A problem first investigated by Hadwiger, who proved c(n) ≥ 2^n + 2^{n-1}.
Burgess and Erdős [Er74b] proved c(n) ≪ n^{n+1}. Connor and Marmorino
[CoMa18] proved c(n) ≥ 2^{n+1} - 1 for all n ≥ 3.
-/

/-- The unit cube [0,1]^n in ℝⁿ. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- An axis-aligned cube in ℝⁿ with given corner and side length. -/
def axisCube {n : ℕ} (corner : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, corner i ≤ x i ∧ x i ≤ corner i + s}

/-- The interior of an axis-aligned cube in ℝⁿ. -/
def axisCubeInterior {n : ℕ} (corner : Fin n → ℝ) (s : ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, corner i < x i ∧ x i < corner i + s}

/-- The n-dimensional unit cube [0,1]^n can be decomposed into exactly k
    homothetic cubes (axis-aligned cubes with positive side lengths) such that
    the cubes cover the unit cube and have pairwise disjoint interiors. -/
def CanDecomposeUnitCube (n k : ℕ) : Prop :=
  ∃ (corners : Fin k → Fin n → ℝ) (sides : Fin k → ℝ),
    (∀ j, sides j > 0) ∧
    (∀ j, axisCube (corners j) (sides j) ⊆ unitCube n) ∧
    (∀ x ∈ unitCube n, ∃ j, x ∈ axisCube (corners j) (sides j)) ∧
    (∀ i j, i ≠ j → ∀ x,
      ¬(x ∈ axisCubeInterior (corners i) (sides i) ∧
        x ∈ axisCubeInterior (corners j) (sides j)))

/--
Erdős Problem #769 [Er74b]:

Let c(n) be minimal such that if k ≥ c(n) then the n-dimensional unit cube
can be decomposed into k homothetic n-dimensional cubes. Is it true that
c(n) ≫ n^n?

Formalized as: there exists C > 0 and N₀ such that for all n ≥ N₀,
if every k ≥ m permits a decomposition of the unit n-cube into k homothetic
cubes, then m ≥ C · n^n (i.e., the threshold c(n) ≥ C · n^n).
-/
theorem erdos_problem_769 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ m : ℕ, (∀ k : ℕ, k ≥ m → CanDecomposeUnitCube n k) →
        (m : ℝ) ≥ C * (n : ℝ) ^ n :=
  sorry

end
