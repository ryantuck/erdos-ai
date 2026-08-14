import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1169

/-!
# Erdős Problem #1169

Is it true that, for all finite k < ω (equivalently, for k = 3),
  ω₁² ↛ (ω₁², k)²?

A problem of Erdős and Hajnal. Hajnal [Ha71] proved this is true assuming the
continuum hypothesis. Status (erdosproblems.com, page edition 25 January 2026;
teorth/erdosproblems metadata mirror, 2026-01-24): NOT DISPROVABLE — "Open in
general, but there exist models of set theory where the result is true."
(Note: this is weaker than independence from ZFC — provability in ZFC is open,
only refutability is ruled out, via Hajnal's CH models.)

The source page displays the formula with the instance k = 3 while quantifying
"for all finite k < ω" in prose; the two readings agree, since a homogeneous
set of order type k ≥ 3 contains one of order type 3, so the k = 3 case of the
negative relation implies all k ≥ 3, and the cases k ≤ 2 are trivially false
(see `erdos_1169`'s docstring).

See also Erdős Problem #592 for a similar problem concerning countable
ordinals, and #1171/#1172 for neighbouring Erdős–Hajnal ordinal partition
problems (with which this file shares its `omega1` and `OrdinalPartitionPair`
definitions verbatim).

References:

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §7.85. (Site-wide key expansion recovered from the original pipeline's
  fetches of erdosproblems.com/latex pages for sibling problems; stub —
  no fuller bibliographic data available offline.)
[Ha71] Hajnal, A., _A negative partition relation_. Proceedings of the
  National Academy of Sciences U.S.A. (1971), 142-144. (From the pipeline's
  fetch of erdosproblems.com/latex/1169; volume number not recovered.)

Tags: set theory, ramsey theory
-/

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The ordinal partition relation α → (β, γ)² for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below α, there is either
    a homogeneous set of order type β in the first color (encoded `true`),
    or a homogeneous set of order type γ in the second color (encoded
    `false`). Formalized via strictly monotone embeddings: a subset of order
    type β corresponds to a strictly monotone function from {x | x < β} to
    {x | x < α}. -/
def OrdinalPartitionPair (α β γ : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Bool,
    (∃ g : {x : Ordinal // x < β} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < β}, i < j → f (g i) (g j) = true) ∨
    (∃ g : {x : Ordinal // x < γ} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < γ}, i < j → f (g i) (g j) = false)

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal.{0}) ^ aleph 0 = aleph 1

/--
Erdős Problem #1169 [Va99, 7.85] (Erdős and Hajnal):

Is it true that, for all finite k with 3 ≤ k < ω,
  ω₁² ↛ (ω₁², k)²?

That is, for every natural number k ≥ 3, there exists a 2-coloring of the
pairs of ordinals below ω₁² such that no subset of order type ω₁² is
monochromatic in the first color and no subset of order type k is
monochromatic in the second color.

The restriction to k ≥ 3 is necessary: for k ≤ 2 the positive relation
ω₁² → (ω₁², k)² holds trivially (for k ≤ 1 the empty/singleton set is
vacuously homogeneous; for k = 2, any coloring with no second-color pair is
constant in the first color on all pairs, making the whole set homogeneous),
so the unrestricted ∀ k statement is provably false in ZFC. The source page
quantifies "for all finite k < ω" in prose while displaying the k = 3
instance, which is equivalent to the k ≥ 3 statement.

Hajnal proved this holds assuming the Continuum Hypothesis [Ha71]; see
`erdos_1169_hajnal_CH`. The problem is "not disprovable": open in ZFC, but
true in some models (whether it is provable in ZFC is open — it is not known
to be independent).

See also Erdős Problem #592 for a similar problem concerning countable
ordinals.

Tags: set theory, ramsey theory
-/
theorem erdos_1169 (k : ℕ) (hk : 3 ≤ k) :
    ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) :=
  sorry

/--
Variant (solved, [Ha71]): Hajnal proved that, assuming the Continuum
Hypothesis, ω₁² ↛ (ω₁², k)² holds for every finite k ≥ 3 (the k = 3 case,
displayed on the source page, implies all k ≥ 3). This is the sense in which
Erdős Problem #1169 is "not disprovable": the negative relation holds in
every model of ZFC + CH.
-/
theorem erdos_1169_hajnal_CH (h : CH) (k : ℕ) (hk : 3 ≤ k) :
    ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) :=
  sorry

end Erdos1169
