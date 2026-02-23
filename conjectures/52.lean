import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #52

The sum-product problem. Let $A$ be a finite set of integers. Is it true that
for every $\epsilon > 0$,
$$\max(|A+A|, |AA|) \gg_\epsilon |A|^{2-\epsilon}?$$

That is, for every $\epsilon > 0$ there exists a constant $c > 0$ (depending on
$\epsilon$) such that for every finite set $A \subseteq \mathbb{Z}$,
$$\max(|A+A|, |A \cdot A|) \geq c \cdot |A|^{2-\epsilon}.$$

A problem of Erdős and Szemerédi [ErSz83]. The current best lower bound is
$\max(|A+A|, |AA|) \gg |A|^{1270/951 - o(1)}$ due to Bloom [Bl25].

Tags: number theory, additive combinatorics
-/

/--
**Erdős Problem #52** (The Sum-Product Conjecture):

For every $\epsilon > 0$, there exists $c > 0$ such that for every finite set
$A$ of integers with $|A| \geq 2$,
$$\max(|A + A|, |A \cdot A|) \geq c \cdot |A|^{2 - \epsilon}.$$
-/
theorem erdos_52 :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ (2 - ε) :=
  sorry

end
