import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
open Set Finset

/--
The set of "infinitely often" differences of A: a natural number d belongs to
D(A) if there are infinitely many pairs (a₁, a₂) ∈ A × A with a₁ - a₂ = d.
We work in ℕ and require a₂ + d = a₁ to avoid subtraction issues.
-/
def infinitelyOftenDiffSet (A : Set ℕ) : Set ℕ :=
  {d : ℕ | {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.2 + d = p.1}.Infinite}

/--
A set S ⊆ ℕ has **bounded gaps** if there exists N such that every interval
[n, n + N] contains an element of S.
-/
def HasBoundedGaps (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, ∃ d ∈ S, n ≤ d ∧ d ≤ n + N

/--
The upper density of A ⊆ ℕ is positive: there exists δ > 0 such that
|A ∩ {1, …, N}| ≥ δ · N for infinitely many N.
-/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ (∀ x ∈ F, 1 ≤ x ∧ x ≤ N) ∧
        δ * (N : ℝ) ≤ (F.card : ℝ)

/--
Erdős Problem #332 [ErGr80, p.50]:

Let A ⊆ ℕ and D(A) be the set of those numbers which occur infinitely often
as a₁ − a₂ with a₁, a₂ ∈ A. What conditions on A are sufficient to ensure
D(A) has bounded gaps?

Prikry, Tijdeman, Stewart, and others have shown that a sufficient condition
is that A has positive upper density. This formalises that known result.

The broader open question asks for weaker sufficient conditions — for instance,
conditions ensuring D(A) has positive density, or ∑_{d ∈ D(A)} 1/d = ∞, or
even just D(A) ≠ ∅.
-/
theorem erdos_problem_332
    (A : Set ℕ)
    (hA : HasPositiveUpperDensity A) :
    HasBoundedGaps (infinitelyOftenDiffSet A) :=
  sorry
