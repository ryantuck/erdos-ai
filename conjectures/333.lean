import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical

/--
The upper density of A ⊆ ℕ:
  d*(A) = limsup_{N→∞} |A ∩ {0, 1, ..., N-1}| / N
-/
noncomputable def upperDensity333 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #333 [ErGr80] (DISPROVED):

Let A ⊆ ℕ be a set of density zero. Does there exist a set B ⊆ ℕ such that
A ⊆ B + B and |B ∩ {1, …, N}| = o(N^{1/2})?

Here B + B = {b₁ + b₂ | b₁, b₂ ∈ B} is the sumset of B with itself, and
o(N^{1/2}) means that |B ∩ {1,…,N}| / N^{1/2} → 0 as N → ∞.

Erdős and Newman [ErNe77] proved this is true when A is the set of squares.
However, Theorem 2 of [ErNe77] already implies a negative answer to this
problem in general, though this was overlooked by Erdős and Graham.
-/
theorem erdos_problem_333 :
    ∀ A : Set ℕ, upperDensity333 A = 0 →
      ∃ B : Set ℕ,
        A ⊆ Set.image2 (· + ·) B B ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            (((Finset.Icc 1 N).filter (· ∈ B)).card : ℝ) ≤ ε * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry
