import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice

noncomputable section

/-!
# Erdős Problem #798

Let t(n) be the minimum number of points in {1,...,n}² such that the C(t,2) lines
determined by these points cover all points in {1,...,n}².

Estimate t(n). In particular, is it true that t(n) = o(n)?

A problem of Erdős and Purdy, who proved t(n) ≫ n^{2/3}.
Resolved by Alon [Al91] who proved t(n) ≪ n^{2/3} log n, confirming t(n) = o(n).
-/

/-- Three points in ℤ × ℤ are collinear if the cross product of the displacement
    vectors from the first point is zero. -/
def IntGridCollinear (p q r : ℤ × ℤ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A finite set S of points in {1,...,n}² covers the grid if every point
    in {1,...,n}² lies on a line determined by two distinct points of S. -/
def CoversIntGrid (n : ℕ) (S : Finset (ℤ × ℤ)) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 ≤ ↑n ∧ 1 ≤ p.2 ∧ p.2 ≤ ↑n) ∧
  ∀ (p : ℤ × ℤ), 1 ≤ p.1 → p.1 ≤ ↑n → 1 ≤ p.2 → p.2 ≤ ↑n →
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ IntGridCollinear a b p

/-- t(n): the minimum number of points in {1,...,n}² whose pairwise lines
    cover all n² grid points. -/
noncomputable def gridCoveringNumber (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (ℤ × ℤ), S.card = k ∧ CoversIntGrid n S}

/--
Erdős Problem #798 (proved by Alon [Al91]):

t(n) = o(n), i.e., the minimum number of points in {1,...,n}² whose lines
cover all grid points is sublinear in n.

Equivalently: for every ε > 0, there exists N₀ such that for all n ≥ N₀,
t(n) ≤ ε · n.
-/
theorem erdos_problem_798 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (gridCoveringNumber n : ℝ) ≤ ε * (n : ℝ) :=
  sorry

end
