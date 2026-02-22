import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Finset Classical

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #840

Let $f(N)$ be the size of the largest quasi-Sidon subset $A\subset\{1,\ldots,N\}$,
where we say that $A$ is quasi-Sidon if $|A+A|=(1+o(1))\binom{|A|}{2}$.
How does $f(N)$ grow?

Erdős and Freud [ErFr91] proved
$(2/\sqrt{3}+o(1))N^{1/2} \leq f(N) \leq (2+o(1))N^{1/2}$.

The upper bound was improved by Pikhurko [Pi06] to
$f(N) \leq ((1/4+1/(\pi+2)^2)^{-1/2}+o(1))N^{1/2} \approx 1.863 N^{1/2}$.

Tags: additive combinatorics, sidon sets
-/

/-- A finite set of natural numbers is δ-quasi-Sidon if |A + A| ≥ (1 - δ) · C(|A|, 2).
    A sequence of sets is quasi-Sidon iff for every δ > 0 it is eventually δ-quasi-Sidon. -/
def IsQuasiSidon (δ : ℝ) (A : Finset ℕ) : Prop :=
  ((A + A).card : ℝ) ≥ (1 - δ) * (Nat.choose A.card 2 : ℝ)

/-- The maximum size of a δ-quasi-Sidon subset of {1, ..., N}. -/
noncomputable def erdos840_f (δ : ℝ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter (fun A => IsQuasiSidon δ A)).sup Finset.card

/--
**Erdős Problem #840** — Lower bound (Erdős–Freud [ErFr91]):

For every ε > 0 and δ > 0, for sufficiently large N,
$f_δ(N) \geq (2/\sqrt{3} - \varepsilon) \cdot \sqrt{N}$.
-/
theorem erdos_840_lower :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (erdos840_f δ N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ) :=
  sorry

/--
**Erdős Problem #840** — Upper bound (Pikhurko [Pi06]):

For every ε > 0 and δ > 0, for sufficiently large N,
$f_δ(N) \leq ((1/4 + 1/(π+2)^2)^{-1/2} + \varepsilon) \cdot \sqrt{N}$.

The constant $(1/4 + 1/(π+2)^2)^{-1/2} = 1.863\cdots$.
-/
theorem erdos_840_upper :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (erdos840_f δ N : ℝ) ≤
      (Real.sqrt ((1 / 4 + 1 / (Real.pi + 2) ^ 2)⁻¹) + ε) * Real.sqrt (N : ℝ) :=
  sorry

end
