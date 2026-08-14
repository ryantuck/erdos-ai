import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1170

/-!
# Erdős Problem #1170

Is it consistent that
  ω₂ → (α)²₂
for every α < ω₂?

The arrow notation κ → (α)²₂ denotes the ordinal partition relation: for
every 2-coloring of the pairs of ordinals below κ, there exists a
monochromatic set of order type α.

Status: OPEN (erdosproblems.com/1170, page last edited 23 January 2026,
accessed 2026-02-23; cross-checked against the teorth/erdosproblems metadata
mirror, status last updated 2026-01-23, formalised: no).

This is a consistency question — is there a model of ZFC in which the
property holds? Lean cannot express provability/consistency over ZFC
directly, so, following the archived styled formalization of this problem,
the *property itself* is formalized below; proving it would in particular
witness the affirmative answer, but the meta-level question is out of reach
of the object-level statement.

Known partial results (from the problem page):
- Laver [La82] proved the consistency of ω₂ → (ω₁·2+1, α)² for all α < ω₂.
- Foreman and Hajnal [FoHa03] proved the consistency of ω₂ → (ω₁²+1, α)²
  for all α < ω₂.

References:

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999. This
problem is item 7.86. (Bibliographic stub: the expansion of the site-wide
key [Va99] was recovered from the archived fetch of
erdosproblems.com/latex/1172 — a sibling problem citing the same key —
since the archived fetch of /latex/1170 itself carried no [Va99] entry.
Not fabricated; no fuller publication data is recoverable offline.)

[La82] Laver, R., _An (ℵ₂, ℵ₂, ℵ₀)-saturated ideal on ω₁_ (1982), 173–180.
(Bibliographic stub recovered from the archived fetch of
erdosproblems.com/latex/1170; journal/volume were not present in the
recovered extraction and are deliberately not invented.)

[FoHa03] Foreman, M. and Hajnal, A., _A partition relation for successors
of large cardinals_, Math. Ann. (2003), 583–623. (Volume number absent from
the recovered extraction; deliberately not invented.)

No related OEIS sequences (metadata mirror: "N/A").

Tags: set theory, ramsey theory
-/

/-- ω₂, the second uncountable ordinal (initial ordinal of cardinality ℵ₂). -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- The ordinal partition relation κ → (α)²₂: for every 2-coloring of increasing
    pairs of ordinals below κ, there exists a monochromatic set of order type α.
    Formalized via strictly monotone embeddings: a subset of order type α corresponds
    to a strictly monotone function from {x | x < α} to {x | x < κ}.

    The coloring is taken as a total function on ordered pairs; only its values on
    increasing pairs (g i, g j), i < j, are constrained, which is equivalent to the
    standard formulation via colorings of unordered 2-element subsets. For α ≤ 1 the
    relation holds vacuously (the homogeneity condition has no instances), matching
    the informal convention. -/
def OrdinalPartition (κ α : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < κ} → {x : Ordinal // x < κ} → Bool,
    ∃ (c : Bool) (g : {x : Ordinal // x < α} → {x : Ordinal // x < κ}),
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < α}, i < j → f (g i) (g j) = c

/--
Erdős Problem #1170 [Va99, 7.86]:

Is it consistent that ω₂ → (α)²₂ for every α < ω₂?

The arrow notation κ → (α)²₂ denotes the ordinal partition relation: for every
2-coloring of pairs of ordinals below κ, there exists a monochromatic set of
order type α.

This is a consistency question: is there a model of ZFC in which this holds?
We formalize the property itself; the statement below is the direct assertion
of that property (this raw corpus has no `answer()` elaborator), and the
meta-level consistency question is documented in the module docstring. The
problem is OPEN.

Known partial results:
- Laver [La82] proved the consistency of ω₂ → (ω₁·2+1, α)² for all α < ω₂.
- Foreman–Hajnal [FoHa03] proved the consistency of ω₂ → (ω₁²+1, α)² for all α < ω₂.
-/
theorem erdos_problem_1170 :
    ∀ α : Ordinal, α < omega2 →
      OrdinalPartition omega2 α :=
  sorry

end Erdos1170

end
