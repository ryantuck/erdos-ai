import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #171

The density Hales-Jewett theorem: for every ε > 0 and integer t ≥ 1, if N is
sufficiently large and A is a subset of [t]^N of size at least ε · t^N then A
must contain a combinatorial line.

A combinatorial line in [t]^N is a set {p₁, ..., p_t} where there is a
non-empty set S of "active" coordinates such that for each active coordinate j,
the j-th coordinate of pᵢ is i, and for each inactive coordinate j, all points
share the same constant value.

This was proved by Furstenberg and Katznelson [FuKa91]. A new elementary proof
with quantitative bounds was given by the Polymath project [Po12].
-/

/-- A combinatorial line in [t]^N is a family of t points parametrized by Fin t,
    determined by a non-empty set S of "active" coordinates and fixed values c
    for inactive coordinates. The i-th point has coordinate j equal to i if j is
    active, and equal to c j if j is inactive. -/
def IsCombLine (t N : ℕ) (P : Fin t → (Fin N → Fin t)) : Prop :=
  ∃ (S : Finset (Fin N)) (c : Fin N → Fin t),
    S.Nonempty ∧
    ∀ (i : Fin t) (j : Fin N),
      P i j = if j ∈ S then i else c j

/--
Erdős Problem #171 (Density Hales-Jewett theorem) [ErGr79, ErGr80]:

For every ε > 0 and integer t ≥ 1, there exists N₀ such that for all N ≥ N₀,
every subset A of [t]^N with |A| ≥ ε · t^N contains a combinatorial line.
-/
theorem erdos_problem_171 :
    ∀ (t : ℕ), 1 ≤ t →
    ∀ (ε : ℝ), 0 < ε →
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset (Fin N → Fin t)),
    (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
    ∃ (P : Fin t → (Fin N → Fin t)),
      IsCombLine t N P ∧ ∀ (i : Fin t), P i ∈ A :=
  sorry
