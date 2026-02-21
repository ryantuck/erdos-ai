import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum

open Cardinal

/-- The negative square-bracket partition relation κ ↛ [μ]ₖ² for cardinals.

    There exists a k-coloring of pairs from a set of cardinality κ such that
    every subset of cardinality ≥ μ contains pairs of all k colors.

    In standard Erdős-Rado partition calculus notation, this is κ ↛ [μ]ₖ². -/
def NegSqBracketPartition (κ μ : Cardinal) (k : ℕ) : Prop :=
  ∃ (α : Type*) (_ : #α = κ) (f : α → α → Fin k),
    (∀ x y, f x y = f y x) ∧
    ∀ (S : Set α), #S ≥ μ →
      ∀ c : Fin k, ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f a b = c

/--
Erdős Problem #474 (1954) [Er95d, p.64] [Va99, 7.81]:

Does the negative square-bracket partition relation 2^ℵ₀ ↛ [ℵ₁]₃² hold?
In words: can the pairs from ℝ be 3-colored so that every uncountable
subset contains pairs of each color?

Sierpinski and Kurepa independently proved the 2-color version (2^ℵ₀ ↛ [ℵ₁]₂²)
holds in ZFC. Erdős proved that under the continuum hypothesis (𝔠 = ℵ₁),
the 3-color version holds, and offered $100 for deciding what happens without CH.

Shelah [Sh88] showed it is consistent without CH that the positive relation
2^ℵ₀ → [ℵ₁]₃² holds, but with 𝔠 very large.

The specific remaining open question (asked in [Va99]):
Assuming 𝔠 = ℵ₂, does 2^ℵ₀ ↛ [ℵ₁]₃² hold?
-/
theorem erdos_problem_474 :
    continuum = aleph 2 →
    NegSqBracketPartition continuum (aleph 1) 3 :=
  sorry
