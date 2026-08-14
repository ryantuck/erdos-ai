import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1171

/-!
# Erdős Problem #1171

Is it true that, for all finite k < ω,
  ω₁² → (ω₁·ω, 3, …, 3)²_{k+1}?

The arrow notation α → (β₀, β₁, …, β_k)² denotes the ordinal partition
relation: for every (k+1)-coloring of the pairs of ordinals below α, there
is some color c and a set homogeneous in color c whose order type is the
c-th target. Here the targets are ω₁·ω for color 0 and 3 (a monochromatic
triple) for each of the remaining k colors.

Status: OPEN (erdosproblems.com/1171, page last edited 26 January 2026,
accessed 2026-02-23; cross-checked against the teorth/erdosproblems metadata
mirror, status last updated 2026-01-23, formalised: no).

The problem is a yes/no question; this raw corpus has no `answer()`
elaborator, so, following the corpus convention for open yes/no questions,
the statement below directly asserts the asked ("yes") direction with a
`sorry` proof.

Known partial results (from the problem page):
- Baumgartner [Ba89b] proved that, assuming a form of Martin's axiom,
  ω₁·ω → (ω₁·ω, 3)². (This is a conditional result about the smaller source
  ordinal ω₁·ω; Martin's axiom is not formalizable from the constructs in
  this file, so no variant is stated for it.)

References:

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999. This
problem is item 7.84. (Bibliographic stub: the expansion of the site-wide
key [Va99] was recovered from the archived fetch of
erdosproblems.com/latex/1172 — a sibling problem citing the same key —
since the archived fetch of /latex/1171 itself carried no [Va99] entry.
Not fabricated; no fuller publication data is recoverable offline.)

[Ba89b] Baumgartner, J. E., _Remarks on partition ordinals_ (1989), 5–17.
(Bibliographic stub recovered from the archived fetch of
erdosproblems.com/latex/1171; the journal/volume were not present in the
recovered extraction and are deliberately not invented.)

No related OEIS sequences (metadata mirror: "N/A").

Tags: set theory, ramsey theory
-/

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The multi-color ordinal partition relation α → (target₀, target_rest, ..., target_rest)²
    with (k+1) colors, where target_rest appears k times. For every (k+1)-coloring of
    pairs of ordinals below α, either there is a homogeneous set of order type target₀
    for color 0, or there exists some color c > 0 with a homogeneous set of order type
    target_rest.

    The coloring is taken as a total function on ordered pairs; only its values on
    increasing pairs (g i, g j), i < j, are constrained, which is equivalent to the
    standard formulation via colorings of unordered 2-element subsets. For k = 0 the
    second disjunct is unsatisfiable (`Fin 1` has no positive element), so the relation
    reduces to the single-color case, matching the informal convention. -/
def OrdinalPartitionMulticolor (α : Ordinal) (k : ℕ) (target₀ target_rest : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Fin (k + 1),
    (∃ g : {x : Ordinal // x < target₀} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < target₀}, i < j → f (g i) (g j) = 0) ∨
    (∃ c : Fin (k + 1), 0 < c.val ∧
      ∃ g : {x : Ordinal // x < target_rest} → {x : Ordinal // x < α},
        StrictMono g ∧
        ∀ i j : {x : Ordinal // x < target_rest}, i < j → f (g i) (g j) = c)

/--
Erdős Problem #1171 [Va99, 7.84]:

Is it true that, for all finite k < ω,
  ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1}?

That is, for every (k+1)-coloring of pairs of ordinals below ω₁², either
there is a homogeneous set of order type ω₁·ω for the first color, or
there is a monochromatic triple for one of the remaining k colors.

The problem is OPEN. Baumgartner [Ba89b] proved that, assuming a form of
Martin's axiom, ω₁·ω → (ω₁·ω, 3)².
-/
theorem erdos_problem_1171 (k : ℕ) :
    OrdinalPartitionMulticolor (omega1 ^ 2) k (omega1 * omega0) 3 :=
  sorry

end Erdos1171

end
