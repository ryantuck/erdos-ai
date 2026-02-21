import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #163

The Burr-Erdős conjecture: For any d ≥ 1, if H is a graph on n vertices such
that every subgraph of H contains a vertex of degree at most d (i.e., H is
d-degenerate), then R(H) ≤ C_d · n for some constant C_d depending only on d.

Here R(H) denotes the diagonal Ramsey number R(H, H): the minimum N such that
every 2-colouring of the edges of K_N contains a monochromatic copy of H.

This is equivalent to: if H is the union of c forests then R(H) ≤ C_c · n;
and also if every subgraph has average degree at most d then R(H) ≤ C_d · n.

Proved by Lee [Le17], who showed R(H) ≤ 2^{2^{O(d)}} · n.
-/

/-- An injective graph homomorphism from H to G: G contains a (not necessarily
    induced) copy of H as a subgraph. -/
def containsCopy {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- A simple graph H on a finite vertex type is d-degenerate if every nonempty
    subset S of vertices contains a vertex v with at most d neighbours in S. -/
def IsDDegenerate {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, (S.filter (H.Adj v)).card ≤ d

/-- The diagonal Ramsey number R(H): the minimum N such that for every simple
    graph G on Fin N, either G or Gᶜ contains a copy of H. -/
noncomputable def ramseyDiag {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsCopy G H ∨ containsCopy Gᶜ H}

/--
Erdős Conjecture (Problem #163) [BuEr75, Er82e] — The Burr-Erdős Conjecture:

For every d ≥ 1, there exists a constant C_d > 0 such that for every
d-degenerate graph H on n vertices, R(H, H) ≤ C_d · n.

Equivalently, if H is the union of c forests then R(H) ≤ C_c · n.

Proved by Lee [Le17], who showed R(H) ≤ 2^{2^{O(d)}} · n.
-/
theorem erdos_problem_163 :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d →
      (ramseyDiag H : ℝ) ≤ C * (n : ℝ) :=
  sorry

end
