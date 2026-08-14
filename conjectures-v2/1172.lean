import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1172

/-!
# Erdős Problem #1172

Establish whether the following are true assuming the generalised continuum hypothesis:
  ω₃ → (ω₂, ω₁+2)²
  ω₃ → (ω₂+ω₁, ω₂+ω)²
  ω₂ → (ω₁^(ω+2)+2, ω₁+2)²

Establish whether the following is true assuming the continuum hypothesis:
  ω₂ → (ω₁+ω)²₂

A problem of Erdős and Hajnal [Va99, 7.87]. Status (erdosproblems.com, page edition
23 January 2026, accessed 2026-02-23; teorth/erdosproblems metadata mirror, last
update 2026-01-23): OPEN — "This is open, and cannot be resolved with a finite
computation."

The source page's remarks recall that the Erdős-Rado partition theorem [ErRa56]
states that (2^κ)⁺ → (κ⁺+1)²_κ for every infinite cardinal κ, and caution:
"The right-hand side of the first and final statements are missing from the
truncated photocopy available of [Va99], and it is possible they have been
filled in incorrectly." In the page's list of four statements, "first and final"
refers to the first GCH statement ω₃ → (ω₂, ω₁+2)² and the CH statement
ω₂ → (ω₁+ω)²₂. Indeed, as displayed, the first statement already follows from
[ErRa56] under GCH (see `erdos_problem_1172_erdos_rado_GCH`), which is consistent
with its right-hand side having been reconstructed too weakly.

This file shares its `omega1`/`omega2` and `OrdinalPartitionPair` definitions
verbatim with the neighbouring Erdős–Hajnal ordinal partition files
#1169/#1170/#1171, and its `GCH` definition with #1173.

References:

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §7.87. (Site-wide key expansion recovered from the original pipeline's fetch
  of erdosproblems.com/latex/1172; stub — no fuller bibliographic data
  available offline.)
[ErRa56] Erdős, P. and Rado, R., _A partition calculus in set theory_. Bulletin
  of the American Mathematical Society (1956), 427-489. (From the pipeline's
  fetch of erdosproblems.com/latex/1172; volume number not recovered.)

Tags: set theory, ramsey theory
-/

/-- ω, the first infinite ordinal. -/
noncomputable def omega0 : Ordinal := (aleph 0).ord

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- ω₂, the second uncountable ordinal. -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- ω₃, the third uncountable ordinal. -/
noncomputable def omega3 : Ordinal := (aleph 3).ord

/-- The ordinal partition relation α → (β, γ)² for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below α, there is either
    a homogeneous set of order type β in the first color (encoded `true`),
    or a homogeneous set of order type γ in the second color (encoded
    `false`). Formalized via strictly monotone embeddings: a subset of
    order type β corresponds to a strictly monotone function
    from {x | x < β} to {x | x < α}. -/
def OrdinalPartitionPair (α β γ : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Bool,
    (∃ g : {x : Ordinal // x < β} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < β}, i < j → f (g i) (g j) = true) ∨
    (∃ g : {x : Ordinal // x < γ} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < γ}, i < j → f (g i) (g j) = false)

/-- The Generalized Continuum Hypothesis: 2^(ℵ_o) = ℵ_{o+1} for all ordinals o. -/
def GCH : Prop := ∀ o : Ordinal.{0}, (2 : Cardinal.{0}) ^ aleph o = aleph (o + 1)

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal.{0}) ^ aleph 0 = aleph 1

/--
Erdős Problem #1172, Part 1 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₃ → (ω₂, ω₁+2)²

This is an open problem of Erdős and Hajnal. The right-hand side of this (the
first) statement is missing from the truncated photocopy available of [Va99]
and may have been filled in incorrectly. Note that, as displayed, this
statement already follows under GCH from the Erdős-Rado partition theorem
[ErRa56] — see `erdos_problem_1172_erdos_rado_GCH` — so the intended
right-hand side was plausibly stronger.
-/
theorem erdos_problem_1172a (h : GCH) :
    OrdinalPartitionPair omega3 omega2 (omega1 + 2) :=
  sorry

/--
Erdős Problem #1172, Part 2 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₃ → (ω₂+ω₁, ω₂+ω)²

This is an open problem of Erdős and Hajnal.
-/
theorem erdos_problem_1172b (h : GCH) :
    OrdinalPartitionPair omega3 (omega2 + omega1) (omega2 + omega0) :=
  sorry

/--
Erdős Problem #1172, Part 3 [Va99, 7.87]:

Assuming the Generalized Continuum Hypothesis, establish whether
  ω₂ → (ω₁^(ω+2)+2, ω₁+2)²

This is an open problem of Erdős and Hajnal.
-/
theorem erdos_problem_1172c (h : GCH) :
    OrdinalPartitionPair omega2 (omega1 ^ (omega0 + 2) + 2) (omega1 + 2) :=
  sorry

/--
Erdős Problem #1172, Part 4 [Va99, 7.87]:

Assuming the Continuum Hypothesis, establish whether
  ω₂ → (ω₁+ω)²₂

That is, for every 2-coloring of the pairs of ordinals below ω₂, there exists
a monochromatic homogeneous set of order type ω₁+ω. (The balanced relation
α → (β)²₂ is encoded as `OrdinalPartitionPair α β β`.)

This is an open problem of Erdős and Hajnal. The right-hand side of this (the
final) statement is missing from the truncated photocopy available of [Va99]
and may have been filled in incorrectly.
-/
theorem erdos_problem_1172d (h : CH) :
    OrdinalPartitionPair omega2 (omega1 + omega0) (omega1 + omega0) :=
  sorry

/--
Context (solved, [ErRa56]): the 2-color instance, under GCH, of the Erdős-Rado
partition theorem (2^κ)⁺ → (κ⁺+1)²_κ at κ = ℵ₁, quoted in the source page's
remarks. Under GCH, 2^(ℵ₁) = ℵ₂, so (2^(ℵ₁))⁺ = ℵ₃ and the theorem gives
ω₃ → (ω₂+1)²_(ℵ₁), hence in particular ω₃ → (ω₂+1)²₂ (encoded as the balanced
pair relation).

Since ω₂ ≤ ω₂+1 and ω₁+2 ≤ ω₂+1, restricting a homogeneous set of order type
ω₂+1 (in either color) shows that this statement implies Part 1 as displayed
(`erdos_problem_1172a`).
-/
theorem erdos_problem_1172_erdos_rado_GCH (h : GCH) :
    OrdinalPartitionPair omega3 (omega2 + 1) (omega2 + 1) :=
  sorry

end Erdos1172

end
