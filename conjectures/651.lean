import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #651

Let $f_k(n)$ denote the smallest integer such that any $f_k(n)$ points in
general position in $\mathbb{R}^k$ contain $n$ which determine a convex
polyhedron. Is it true that
  f_k(n) > (1 + c_k)^n
for some constant $c_k > 0$?

This is the higher-dimensional generalization of the Erdős-Klein-Szekeres
conjecture (see problem #107 for k = 2). One can show that
  f_2(n) > f_3(n) > ⋯.

DISPROVED: Pohoata and Zakharov [PoZa22] proved that f_3(n) ≤ 2^{o(n)},
which shows that f_k(n) need not grow exponentially for k ≥ 3.
-/

/-- A finite point set in ℝ^k is in general position if any k+1 distinct
    points are affinely independent (no k+1 points lie on a common
    hyperplane). -/
def InGeneralPositionRk (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ f : Fin (k + 1) → EuclideanSpace ℝ (Fin k),
    (∀ i, f i ∈ P) → Function.Injective f →
    AffineIndependent ℝ f

/-- A finite point set in ℝ^k is in convex position if no point lies in the
    convex hull of the remaining points (the points are the vertices of a
    convex polytope). -/
def InConvexPositionRk (k : ℕ) (S : Finset (EuclideanSpace ℝ (Fin k))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ (↑(S.erase p) : Set (EuclideanSpace ℝ (Fin k)))

/-- f_k(n): the smallest integer m such that any m points in general position
    in ℝ^k contain n points in convex position (forming the vertices of a
    convex polytope). -/
noncomputable def fk (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ P : Finset (EuclideanSpace ℝ (Fin k)),
    P.card = m →
    InGeneralPositionRk k P →
    ∃ Q : Finset (EuclideanSpace ℝ (Fin k)),
      Q ⊆ P ∧ Q.card = n ∧ InConvexPositionRk k Q}

/--
Erdős Problem #651 [Er97e]:

Let f_k(n) denote the smallest integer such that any f_k(n) points in general
position in ℝ^k contain n points forming the vertices of a convex polytope.
The conjecture asks whether f_k(n) grows at least exponentially in n for
each fixed k ≥ 2, i.e., whether there exists c_k > 0 such that
  f_k(n) > (1 + c_k)^n.

DISPROVED for k ≥ 3: Pohoata and Zakharov [PoZa22] proved f_3(n) ≤ 2^{o(n)}.
-/
theorem erdos_problem_651 (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (fk k n : ℝ) > (1 + c) ^ n :=
  sorry

end
