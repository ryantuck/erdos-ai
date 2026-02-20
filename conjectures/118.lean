import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.Hom.Basic

open Ordinal

/-- The "underlying type" of ordinal `α`: the set of all ordinals strictly less
    than `α`, linearly ordered by the natural ordering on ordinals. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- The ordinal partition relation `α → (β, γ)²`:
    Every 2-coloring of the pairs of elements of `α` (viewed as the linearly
    ordered set `{0, 1, ..., α)`) contains either:
    - an order-embedded copy of `β` whose pairs are all colored 0 (red), or
    - an order-embedded copy of `γ` whose pairs are all colored 1 (blue).

    Here a "copy of β" is given by an order embedding `e : OrdinalSet β ↪o OrdinalSet α`,
    and monochromaticity means `f (e i) (e j) = c` for all `i < j`. -/
def OrdPartition (α β γ : Ordinal) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ e : OrdinalSet γ ↪o OrdinalSet α,
      ∀ i j : OrdinalSet γ, i < j → f (e i) (e j) = 1)

/--
Erdős–Hajnal Conjecture on Partition Ordinals (Problem #118)
[Er87, Er90, Er95d, Er97f] — **DISPROVED**

An ordinal `α` is called a *partition ordinal* if `α → (α, 3)²`, i.e., every
2-coloring of pairs from a linearly ordered set of order type `α` contains either
a monochromatic copy of `α` in color 0 (red) or a monochromatic triangle K₃ in
color 1 (blue).

Erdős and Hajnal conjectured that for every partition ordinal `α` and every `n ≥ 3`,
we also have `α → (α, n)²`.

This conjecture is FALSE, as independently shown by Schipperus [Sc99] (published in
[Sc10]) and Darby [Da99].  For example, Larson [La00] showed that `ω^(ω^2)` is a
partition ordinal — i.e., `ω^(ω^2) → (ω^(ω^2), 3)²` holds — but
`ω^(ω^2) → (ω^(ω^2), 5)²` fails.

See also Hajnal–Larson, Chapter 2.9 of [HST10] for background and proof sketches.
-/
theorem erdos_problem_118 :
    ¬ ∀ (α : Ordinal), OrdPartition α α 3 →
      ∀ n : ℕ, 3 ≤ n → OrdPartition α α (↑n) :=
  sorry
