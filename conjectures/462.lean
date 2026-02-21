import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators Filter Real

noncomputable section

/-!
# Erdős Problem #462

Let $p(n)$ denote the least prime factor of $n$. There is a constant $c > 0$
such that
$$\sum_{\substack{n < x \\ n \text{ not prime}}} \frac{p(n)}{n}
  \sim c \frac{x^{1/2}}{(\log x)^2}.$$

Is it true that there exists a constant $C > 0$ such that
$$\sum_{\substack{x \leq n \leq x + C x^{1/2} (\log x)^2 \\ n \text{ not prime}}}
  \frac{p(n)}{n} \gg 1$$
for all large $x$?
-/

/--
Erdős Problem #462 (Background asymptotic) [ErGr80, p.92]:

There exists a constant $c > 0$ such that the sum of $p(n)/n$ over composite
$n \leq x$ is asymptotic to $c \cdot \sqrt{x} / (\log x)^2$, where $p(n)$
denotes the least prime factor of $n$.
-/
theorem erdos_problem_462_asymptotic :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun x : ℕ =>
        (∑ n ∈ (Finset.Icc 2 x).filter (fun n => ¬ Nat.Prime n),
          (Nat.minFac n : ℝ) / (n : ℝ)) /
        (Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ 2))
        atTop (nhds c) :=
  sorry

/--
Erdős Problem #462 [ErGr80, p.92]:

Is it true that there exists a constant $C > 0$ such that the sum of $p(n)/n$
over composite $n$ in $[x, x + C\sqrt{x}(\log x)^2]$ is $\gg 1$ for all
large $x$? Here $p(n)$ denotes the least prime factor of $n$.
-/
theorem erdos_problem_462 :
    ∃ C : ℝ, C > 0 ∧ ∃ δ : ℝ, δ > 0 ∧ ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      δ ≤ ∑ n ∈ (Finset.Icc x
        (x + ⌊C * Real.sqrt (x : ℝ) * (Real.log (x : ℝ)) ^ 2⌋₊)).filter
        (fun n => ¬ Nat.Prime n),
        (Nat.minFac n : ℝ) / (n : ℝ) :=
  sorry

end
