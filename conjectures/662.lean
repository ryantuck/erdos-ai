import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #662

Consider the triangular lattice with minimal distance between two points 1.
Denote by f(t) the number of lattice points within distance t of any fixed
lattice point. For example f(1) = 6, f(√3) = 12.

Let x₁, ..., xₙ ∈ ℝ² be such that d(xᵢ, xⱼ) ≥ 1 for all i ≠ j. Is it true
that, provided n is sufficiently large depending on t, the number of ordered
pairs (i, j) with i ≠ j and d(xᵢ, xⱼ) ≤ t is at most n · f(t)?

Note: The original problem statement in [Er97e] contains apparent typos and is
acknowledged as ambiguous. This formalization captures what appears to be the
most natural interpretation: among unit-separated point sets, the triangular
lattice maximizes the number of close pairs.

A problem of Erdős, Lovász, and Vesztergombi.

Tags: geometry | distances
-/

open Classical

/-- f(t) = the number of integer pairs (a, b) ≠ (0, 0) with a² + ab + b² ≤ t²,
    which equals the number of neighbors within distance t of any point in the
    triangular lattice (with unit minimal distance). The squared distance from
    the origin to lattice point (a, b) in the triangular lattice is a² + ab + b². -/
noncomputable def triangularLatticeNeighborCount (t : ℝ) : ℕ :=
  Set.ncard {p : ℤ × ℤ | p ≠ (0, 0) ∧
    ((p.1 : ℝ) ^ 2 + (p.1 : ℝ) * (p.2 : ℝ) + (p.2 : ℝ) ^ 2) ≤ t ^ 2}

/-- The number of ordered pairs of distinct points in P with distance at most t. -/
noncomputable def closePairCount
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (t : ℝ) : ℕ :=
  ((P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 ≤ t)).card

/--
**Erdős Problem #662** [Er97e, p.532]:

Among n points in ℝ² with minimum pairwise distance ≥ 1, the number of
ordered pairs at distance ≤ t is at most n · f(t), where f(t) is the number
of neighbors within distance t in the triangular lattice. Equality is
achieved (asymptotically) only by the triangular lattice.

The original statement contains apparent typos; this is the most natural
interpretation of the intended conjecture.
-/
theorem erdos_problem_662 :
    ∀ t : ℝ, t > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
          P.card = n →
          (∀ p ∈ P, ∀ q ∈ P, p ≠ q → dist p q ≥ 1) →
          closePairCount P t ≤ n * triangularLatticeNeighborCount t :=
  sorry
