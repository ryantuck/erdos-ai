import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice

noncomputable section

/-!
# Erdős Problem #960

Let r, k ≥ 2 be fixed. Let A ⊂ ℝ² be a set of n points with no k points
on a line. Determine the threshold f_{r,k}(n) such that if there are at
least f_{r,k}(n) many ordinary lines (lines containing exactly two points)
then there is a set A' ⊆ A of r points such that all C(r,2) many lines
determined by A' are ordinary.

Is it true that f_{r,k}(n) = o(n²), or perhaps even ≪ n?

A problem of Erdős [Er84].
-/

/--
A finite point set in ℝ² has no k collinear if every k-element subset
is not collinear (i.e., no line contains k or more of the points).
-/
def NoKCollinear (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = k → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
An ordinary line of a point set P is a line (1-dimensional affine subspace)
that contains exactly two points of P.
-/
def IsOrdinaryLine (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ L.direction = 1 ∧
  Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L} = 2

/--
The number of ordinary lines determined by a point set P: the number of
lines (1-dimensional affine subspaces) containing exactly two points of P.
-/
noncomputable def ordinaryLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) | IsOrdinaryLine P L}

/--
The line through two distinct points in ℝ²: the affine span of {p, q}.
-/
noncomputable def lineThrough (p q : EuclideanSpace ℝ (Fin 2)) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) :=
  affineSpan ℝ {p, q}

/--
A subset A' ⊆ A of r points has all its determined lines ordinary with
respect to A: for every pair of distinct points p, q ∈ A', the line through
p and q is ordinary (contains exactly two points of A).
-/
def AllPairsOrdinary (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (A' : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A' ⊆ A ∧
  ∀ p ∈ A', ∀ q ∈ A', p ≠ q → IsOrdinaryLine A (lineThrough p q)

/--
f_{r,k}(n): the minimum number of ordinary lines that guarantees the existence
of r points, all of whose C(r,2) determined lines are ordinary.

More precisely, f_{r,k}(n) is the smallest m such that for every set A of n
points in ℝ² with no k collinear and at least m ordinary lines, there exists
A' ⊆ A with |A'| = r such that every line determined by A' is ordinary.
-/
noncomputable def f_rk (r k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = n →
    NoKCollinear k A →
    ordinaryLineCount A ≥ m →
    ∃ A' : Finset (EuclideanSpace ℝ (Fin 2)),
      A'.card = r ∧ AllPairsOrdinary A A'}

/--
Erdős Problem #960 [Er84]:

For fixed r, k ≥ 2, the threshold f_{r,k}(n) is o(n²). That is, for every
ε > 0 there exists N such that for all n ≥ N, f_{r,k}(n) ≤ ε · n².

This is the weaker form of the conjecture. Erdős also asks whether perhaps
f_{r,k}(n) ≪ n (i.e., f_{r,k}(n) = O(n)).
-/
theorem erdos_problem_960 (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (f_rk r k n : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #960, stronger form [Er84]:

For fixed r, k ≥ 2, the threshold f_{r,k}(n) = O(n). That is, there exists
C > 0 such that f_{r,k}(n) ≤ C · n for all n.
-/
theorem erdos_problem_960_strong (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, (f_rk r k n : ℝ) ≤ C * (n : ℝ) :=
  sorry

end
