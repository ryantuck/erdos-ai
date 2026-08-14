import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Erdős Problem #1124

Source: https://www.erdosproblems.com/1124 (full archived HTML capture,
accessed 2026-02-23, recovered from the session logs; a second, structured
capture in the upstream formal-conjectures logs agrees on every field).

Verbatim statement: "Can a square and a circle of the same area be decomposed
into a finite number of congruent parts?"

Status: PROVED (banner tooltip: "This has been solved in the affirmative.").
Problem source: [Er81b, p.30]. Tag: geometry.

Remarks from the page:

* "A problem of Tarski, which Erdős described as 'a very beautiful
  problem...if it were my problem I would offer \$1000 for it'."
* "This is true - Laczkovich [La90b] proved that in fact this is possible
  using translations only." (The translations-only strengthening is
  formalized below as `erdos_problem_1124.variants.translations`.)

Encoding notes.

1. This is Tarski's circle-squaring problem. Concrete representatives: the
   closed unit square $[0,1]^2$ and the closed disk of radius $1/\sqrt{\pi}$
   centered at the origin, both of area $1$. Any square/circle pair of equal
   area is carried to this pair by a single similarity applied simultaneously
   to both sets, and equidecomposability by isometries (or by translations)
   is invariant under such simultaneous scaling, so the representative choice
   is without loss of generality.
2. "Congruent parts" is encoded as: there is a distance-preserving map
   `f : ℝ² → ℝ²` (Mathlib's `Isometry f`, not assumed surjective) with
   `f '' piece_sq = piece_disk`. Any distance-preserving self-map of a
   Euclidean space preserves metric betweenness and is therefore an affine
   rigid motion (automatically surjective), and conversely any isometry
   between two subsets of the plane extends to a rigid motion of the plane,
   so this is exactly planar congruence of the pieces.
3. The source poses a yes/no question ("Can...?"). This raw-file corpus has
   no `answer()` elaborator, so the main theorem directly asserts the
   affirmative answer — the true direction, per Laczkovich [La90b].
4. The pieces are arbitrary subsets: no measurability or topological
   regularity is imposed, matching the problem as posed (Laczkovich's
   construction uses the axiom of choice and carries no measurability
   guarantee for its pieces).

References (keys as on the recovered page):

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981),
27-35 (2nd edition). (Bibliographic data recovered from the site's `/latex`
bibliography for neighboring problems via the session logs — multiple
independent captures agree; the `/latex/1124` capture itself carries no
[Er81b] entry.)

[La90b] Laczkovich, M., _Equidecomposability and discrepancy; a solution of
Tarski's circle-squaring problem_. J. Reine Angew. Math. 404 (*) (1990),
77-117. ((*): journal, year, and pages are recovered from the archived
`/latex/1124` extraction; the volume number was absent there and is carried
from the archived styled sibling `deepmind/deepmind/1124.lean` — it matches
reviewer knowledge of the paper but is NOT site-verified.)

Related OEIS sequences: none listed. Formalised statement in external
databases: No (as of the archived capture). The page records 2 comments
(contents not captured).

NOTE: the additions in this v2 file (module docstring, [Er81b] attribution,
translations variant) are NOT compile-verified — the review container has no
Lean toolchain. The input `conjectures/1124.lean` is recorded as building
successfully in the original pipeline (session log 8c5ed71d: "Build completed
successfully (2388 jobs)", sole warning the expected `sorry`).
-/

noncomputable section

/-- The unit square [0,1]² in ℝ². -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

/--
Erdős Problem #1124 (Tarski's circle-squaring problem, proved):

Can a square and a circle of the same area be decomposed into a finite number
of congruent parts?

A problem of Tarski [Er81b, p.30], which Erdős described as 'a very beautiful
problem...if it were my problem I would offer $1000 for it'.

Laczkovich [La90b] proved that this is possible using translations only; the
translations-only strengthening is stated separately as
`erdos_problem_1124.variants.translations`.

Formally: the unit square and the closed disk of radius 1/√π (both having area 1)
can be partitioned into finitely many pieces such that corresponding pieces are
congruent (related by isometries of ℝ²).
-/
theorem erdos_problem_1124 :
    ∃ (n : ℕ),
    ∃ (pieces_sq pieces_disk : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      -- The pieces partition the unit square
      (⋃ i, pieces_sq i) = unitSquare ∧
      (∀ i j, i ≠ j → Disjoint (pieces_sq i) (pieces_sq j)) ∧
      -- The pieces partition the closed disk of radius 1/√π (same area as unit square)
      (⋃ i, pieces_disk i) = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / Real.sqrt Real.pi) ∧
      (∀ i j, i ≠ j → Disjoint (pieces_disk i) (pieces_disk j)) ∧
      -- Corresponding pieces are congruent (related by an isometry)
      (∀ i, ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
        Isometry f ∧ f '' (pieces_sq i) = pieces_disk i) :=
  sorry

/--
Erdős Problem #1124, translations-only variant — Laczkovich's actual theorem
[La90b], page-confirmed ("Laczkovich [La90b] proved that in fact this is
possible using translations only"):

The unit square and the closed disk of radius 1/√π can be partitioned into
finitely many pieces such that each piece of the square is carried onto the
corresponding piece of the disk by a translation. This is strictly stronger
than `erdos_problem_1124` (every translation is an isometry).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1124.variants.translations :
    ∃ (n : ℕ),
    ∃ (pieces_sq pieces_disk : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      -- The pieces partition the unit square
      (⋃ i, pieces_sq i) = unitSquare ∧
      (∀ i j, i ≠ j → Disjoint (pieces_sq i) (pieces_sq j)) ∧
      -- The pieces partition the closed disk of radius 1/√π (same area as unit square)
      (⋃ i, pieces_disk i) = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / Real.sqrt Real.pi) ∧
      (∀ i j, i ≠ j → Disjoint (pieces_disk i) (pieces_disk j)) ∧
      -- Corresponding pieces are related by translations
      (∀ i, ∃ v : EuclideanSpace ℝ (Fin 2), (· + v) '' (pieces_sq i) = pieces_disk i) :=
  sorry

end
