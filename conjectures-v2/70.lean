import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Ordinal

open Ordinal Cardinal

noncomputable section

/-!
# Erdős Problem #70

Let 𝔠 be the ordinal of the real numbers (i.e. the cardinality of the
continuum, viewed as its initial ordinal), β be any countable ordinal, and
2 ≤ n < ω. Is it true that 𝔠 → (β, n)³₂?

That is, for every 2-coloring of the 3-element increasing sequences of
ordinals below 𝔠, there is either a homogeneous set of order type β for
one color, or a homogeneous set of size n for the other color.

Erdős and Rado proved that 𝔠 → (ω + n, 4)³₂ for any 2 ≤ n < ω.

The instances n ≤ 3 are trivially true: a homogeneous set of size at most 2
carries no triples, and for n = 3 either some triple has color 1 (a
color-1-homogeneous 3-element set) or every triple has color 0 (so any
subset of order type β is color-0-homogeneous). The genuine content of the
question begins at n = 4.

**Status: OPEN** (erdosproblems.com/70, page edition 23 January 2026,
accessed 2026-02-22; teorth/erdosproblems metadata mirror, state "open",
last update 2025-08-31). Following the repository convention for open
conjectures, the theorem below asserts the affirmative (conjectured)
direction of the question.

References (stubs; the site's own bibliography was not recoverable offline):

[Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and
combinatorics (Arcata, Calif., 1985), Contemp. Math. 65 (1987), 223–228.
(Corpus-consensus expansion of the erdosproblems.com key [Er87]; some
sibling files carry conflicting expansions of this key, so treat as
unconfirmed.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
the conference "Paul Erdős and his mathematics", Budapest (1999). Cited for
this problem as [Va99, 7.83].

Tags: graph theory, ramsey theory, set theory
-/

/-- The ordinal partition relation `α → (β, γ)³₂`:
for every 2-coloring of increasing triples from ordinals below `α`,
there is either a homogeneous set of order type `β` for color 0,
or a homogeneous set of order type `γ` for color 1.

A homogeneous set of order type `δ` is given by a strictly increasing
function `g` mapping ordinals below `δ` to ordinals below `α`, such that
all increasing triples in the image of `g` receive the same color. -/
def OrdinalPartition3_2 (α β γ : Ordinal) : Prop :=
  ∀ f : Ordinal → Ordinal → Ordinal → Fin 2,
    (∃ g : Ordinal → Ordinal,
      (∀ i j, i < β → j < β → i < j → g i < g j) ∧
      (∀ i, i < β → g i < α) ∧
      ∀ i j k, i < j → j < k → k < β → f (g i) (g j) (g k) = 0) ∨
    (∃ g : Ordinal → Ordinal,
      (∀ i j, i < γ → j < γ → i < j → g i < g j) ∧
      (∀ i, i < γ → g i < α) ∧
      ∀ i j k, i < j → j < k → k < γ → f (g i) (g j) (g k) = 1)

/--
**Erdős Problem #70** [Er87] [Va99, 7.83]:

Let 𝔠 be the cardinality of the continuum (viewed as an initial ordinal),
β be any countable ordinal, and 2 ≤ n < ω. Is it true that 𝔠 → (β, n)³₂?

The source poses this as an open yes/no question; the statement below
asserts the affirmative (conjectured) direction.
-/
theorem erdos_problem_70 (β : Ordinal) (hβ : β.card ≤ ℵ₀)
    (n : ℕ) (hn : 2 ≤ n) :
    OrdinalPartition3_2 (Cardinal.continuum.ord) β (↑n) :=
  sorry

/--
**Erdős Problem #70, Erdős–Rado partial result** [Er87]:

Erdős and Rado proved that 𝔠 → (ω + n, 4)³₂ for any 2 ≤ n < ω — the
instances of the conjecture with the color-0 order type β = ω + n and the
color-1 size fixed at 4. (Confirmed by the source page's remarks; this
variant statement is not compile-verified.)
-/
theorem erdos_problem_70.variants.erdos_rado (n : ℕ) (hn : 2 ≤ n) :
    OrdinalPartition3_2 (Cardinal.continuum.ord) (omega0 + (n : Ordinal)) (4 : Ordinal) :=
  sorry

end
