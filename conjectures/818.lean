import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #818

Let $A$ be a finite set of integers such that $|A+A| \ll |A|$. Is it true that
$$|AA| \gg \frac{|A|^2}{(\log |A|)^C}$$
for some constant $C > 0$?

A problem of Erdős [Er91]. This was proved by Solymosi [So09d], in the strong form
$|AA| \gg |A|^2 / \log |A|$.

Tags: additive combinatorics
-/

/--
**Erdős Problem #818** (proved by Solymosi [So09d]):

There exists a constant $C > 0$ such that for every $K > 0$, there exists $c > 0$
such that for every finite set $A$ of integers with $|A + A| \leq K \cdot |A|$,
we have $|A \cdot A| \geq c \cdot |A|^2 / (\log |A|)^C$.
-/
theorem erdos_818 :
    ∃ C : ℝ, C > 0 ∧
    ∀ K : ℝ, K > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    ((A + A).card : ℝ) ≤ K * A.card →
    ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ 2 / (Real.log (A.card : ℝ)) ^ C :=
  sorry

end
