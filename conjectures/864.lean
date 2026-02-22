import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset Classical

noncomputable section

/-!
# Erdős Problem #864

Let $A\subseteq \{1,\ldots, N\}$ be a set such that there exists at most one $n$
with more than one solution to $n = a + b$ (with $a \leq b \in A$).
Estimate the maximal possible size of $|A|$ — in particular, is it true that
$|A| \leq (1+o(1))\frac{2}{\sqrt{3}} N^{1/2}$?

A problem of Erdős and Freud [ErFr91], who prove the matching lower bound
$|A| \geq (1+o(1))\frac{2}{\sqrt{3}} N^{1/2}$.

This is a weaker form of [840].

Tags: number theory, sidon sets, additive combinatorics
-/

/-- The number of representations of `n` as `a + b` with `a ≤ b`, `a ∈ A`, `b ∈ A`. -/
def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.filter (fun a => 2 * a ≤ n ∧ (n - a) ∈ A)).card

/-- A set `A` is *almost Sidon* if at most one integer `n` has more than one
    representation as `n = a + b` with `a ≤ b ∈ A`. -/
def IsAlmostSidon (A : Finset ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card ≤ 1 ∧
    ∀ n : ℕ, n ∉ S → sumRepCount A n ≤ 1

/-- The maximum size of an almost Sidon subset of `{1, …, N}`. -/
noncomputable def erdos864_f (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter IsAlmostSidon).sup Finset.card

/--
**Erdős Problem #864** — Conjectured upper bound:

For every ε > 0, for sufficiently large N,
  f(N) ≤ (2/√3 + ε) · √N.
-/
theorem erdos_864_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (erdos864_f N : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt (N : ℝ) :=
  sorry

/--
**Erdős Problem #864** — Lower bound (Erdős–Freud [ErFr91]):

For every ε > 0, for sufficiently large N,
  f(N) ≥ (2/√3 - ε) · √N.
-/
theorem erdos_864_lower :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (erdos864_f N : ℝ) ≥ (2 / Real.sqrt 3 - ε) * Real.sqrt (N : ℝ) :=
  sorry

end
