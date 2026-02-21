import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-!
# Erdős Problem #532

If $\mathbb{N}$ is 2-coloured then is there some infinite set $A\subseteq \mathbb{N}$
such that all finite subset sums $\sum_{n\in S}n$ (as $S$ ranges over all non-empty
finite subsets of $A$) are monochromatic?

In other words, must some colour class be an IP set. Asked by Graham and Rothschild.

Proved by Hindman [Hi74] for any number of colours. This is now known as
**Hindman's theorem** (or the Finite Sums theorem).

See also [531] for the finite version (Folkman numbers).
-/

/-- **Hindman's theorem** (Erdős Problem #532, PROVED [Hi74]):
For any 2-colouring `χ` of the natural numbers, there exists an infinite set
`A` of positive naturals such that all non-empty finite subset sums of elements
of `A` are monochromatic. -/
theorem erdos_problem_532 (χ : ℕ → Bool) :
    ∃ (A : Set ℕ), A.Infinite ∧ (∀ a ∈ A, 0 < a) ∧
    ∃ c : Bool, ∀ S : Finset ℕ, S.Nonempty → (↑S : Set ℕ) ⊆ A →
      χ (∑ i ∈ S, i) = c :=
  sorry
