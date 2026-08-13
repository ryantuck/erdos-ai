import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable

/-!
# Erdős Problem #1071

Is there a finite set of unit line segments (rotated and translated copies of
$(0,1)$) in the unit square, no two of which intersect, which are maximal with
respect to this property?

Is there a region $R$ with a maximal set of disjoint unit line segments that is
countably infinite?

A question of Erdős and Tóth [Er87b, p.173].

Status: PROVED (LEAN) per erdosproblems.com/1071 (page last edited
01 February 2026) — "solved in the affirmative and the proof verified in
Lean"; the problem carried a \$10 prize. The answer to the first question is
yes, which Erdős gave Danzer \$10 for; [Er87b] contains two example
constructions, the first by Danzer, the second by an unnamed participant
(figures not reproduced here). Alexeev has proved (in the site comments) that
the unit square itself admits a countably infinite maximal such set.

Formalization notes: `erdos_problem_1071b` states Alexeev's form of the second
question, with the region instantiated as the unit square. The unrestricted
reading of "region" as an arbitrary subset of the plane would make the
question degenerate — a disjoint union of countably many far-separated open
unit segments is itself such a region — so the unit-square form is the
substantive, page-confirmed statement.

In [Er87b] Erdős further asks what happens if the unit line segments are
rotated/translated copies of $[0,1]$ that are allowed to intersect only at
their endpoints; this open-ended further question is recorded here but not
formalized (the endpoint-intersection notion is ambiguous in the source).

An upstream formalization exists at google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1071.lean`; that file is the authoritative
artifact and is not present in this repository.

Reference: https://www.erdosproblems.com/1071
Tags: geometry

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_.
Intuitive geometry (Siófok, 1985) (1987), 167-177.
-/

open Set

noncomputable section

/-- An open unit segment in ℝ²: the set {p + t • d | 0 < t < 1}. -/
def OpenUnitSegment (p d : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = p + t • d}

/-- The closed unit square [0,1]² in ℝ². -/
def UnitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/--
A family of unit segments in a region R is a maximal pairwise-disjoint family if:
(1) all directions are unit vectors,
(2) every segment lies in R,
(3) distinct segments are disjoint, and
(4) every unit segment contained in R meets some member of the family.
-/
def IsMaximalDisjointFamily
    (R : Set (EuclideanSpace ℝ (Fin 2)))
    (S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ pd ∈ S, ‖pd.2‖ = 1) ∧
  (∀ pd ∈ S, OpenUnitSegment pd.1 pd.2 ⊆ R) ∧
  (∀ pd₁ ∈ S, ∀ pd₂ ∈ S, pd₁ ≠ pd₂ →
    Disjoint (OpenUnitSegment pd₁.1 pd₁.2) (OpenUnitSegment pd₂.1 pd₂.2)) ∧
  (∀ p d : EuclideanSpace ℝ (Fin 2), ‖d‖ = 1 → OpenUnitSegment p d ⊆ R →
    ∃ pd ∈ S, (OpenUnitSegment p d ∩ OpenUnitSegment pd.1 pd.2).Nonempty)

/--
Erdős Problem #1071, first part [Er87b, p.173]:

Is there a finite set of unit line segments (rotated and translated copies of
the open interval (0,1)) in the unit square, no two of which intersect,
which are maximal with respect to this property?

A question of Erdős and Tóth. The answer is yes, proved by Danzer.
-/
theorem erdos_problem_1071a :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      S.Finite ∧ IsMaximalDisjointFamily UnitSquare S :=
  sorry

/--
Erdős Problem #1071, second part [Er87b, p.173]:

Is there a region R with a maximal set of disjoint unit line segments that is
countably infinite?

Alexeev proved that the unit square itself admits a countably infinite maximal
family.
-/
theorem erdos_problem_1071b :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      S.Countable ∧ S.Infinite ∧ IsMaximalDisjointFamily UnitSquare S :=
  sorry

end
