import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Defs

open Classical Filter

noncomputable section

/-!
# Erdős Problem #656

Let A ⊆ ℕ be a set with positive upper density. Must there exist an infinite
set B ⊆ ℕ and integer t such that B + B + t ⊆ A?

A problem of Erdős [Er75b], posed as a candidate for a density version of
Hindman's theorem (see [172]). This was proved by Kra, Moreira, Richter,
and Robertson [KMRR24].

Tags: number theory | additive combinatorics
-/

/-- The upper density of a set A ⊆ ℕ, defined as
    limsup_{N → ∞} |A ∩ {0, ..., N-1}| / N. -/
noncomputable def Nat.upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ =>
    ((Finset.filter (· ∈ A) (Finset.range N)).card : ℝ) / N) atTop

/--
**Erdős Problem #656** [Er75b]:

Let A ⊆ ℕ have positive upper density. Then there exist an infinite set B ⊆ ℕ
and an integer t such that b₁ + b₂ + t ∈ A for all b₁, b₂ ∈ B (where the
arithmetic is in ℤ).

Proved by Kra, Moreira, Richter, and Robertson [KMRR24].
-/
theorem erdos_problem_656 (A : Set ℕ) (hA : Nat.upperDensity A > 0) :
    ∃ (B : Set ℕ) (t : ℤ), Set.Infinite B ∧
      ∀ b₁ ∈ B, ∀ b₂ ∈ B, ∃ a ∈ A, (a : ℤ) = ↑b₁ + ↑b₂ + t :=
  sorry

end
