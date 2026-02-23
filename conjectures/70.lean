import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Ordinal

open Ordinal Cardinal

noncomputable section

/-!
# Erdős Problem #70

Let 𝔠 be the cardinality of the continuum, β be any countable ordinal, and
2 ≤ n < ω. Is it true that 𝔠 → (β, n)²₃?

That is, for every 2-coloring of the 3-element increasing sequences of
ordinals below 𝔠, there is either a homogeneous set of order type β for
one color, or a homogeneous set of size n for the other color.

Erdős and Rado proved that 𝔠 → (ω + n, 4)²₃ for any 2 ≤ n < ω.

Tags: graph theory, ramsey theory, set theory
-/

/-- The ordinal partition relation `α → (β, γ)²₃`:
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
**Erdős Problem #70** [Er87]:

Let 𝔠 be the cardinality of the continuum (viewed as an initial ordinal),
β be any countable ordinal, and 2 ≤ n < ω. Is it true that 𝔠 → (β, n)²₃?
-/
theorem erdos_problem_70 (β : Ordinal) (hβ : β.card ≤ ℵ₀)
    (n : ℕ) (hn : 2 ≤ n) :
    OrdinalPartition3_2 (Cardinal.continuum.ord) β (↑n) :=
  sorry

end
