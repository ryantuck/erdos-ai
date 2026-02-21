import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

noncomputable section

/-!
# Erdős Problem #535

Let $r \geq 3$, and let $f_r(N)$ denote the size of the largest subset of
$\{1, \ldots, N\}$ such that no subset of size $r$ has the same pairwise
greatest common divisor between all elements. Estimate $f_r(N)$.

Erdős [Er64] proved that $f_r(N) \leq N^{3/4+o(1)}$, and Abbott and Hanson
[AbHa70] improved this exponent to $1/2$. Erdős [Er64] proved the lower bound
$f_3(N) > N^{c/\log\log N}$ for some constant $c > 0$, and conjectured this
should also be an upper bound.

This problem is intimately connected with the sunflower problem [20].
-/

/-- A set `A` of natural numbers is `r`-GCD-uniform-free if no `r`-element
subset has all pairwise GCDs equal. That is, there is no `r`-element subset
`S ⊆ A` and value `d` such that `gcd(a, b) = d` for all distinct `a, b ∈ S`. -/
def IsGCDUniformFree (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = r →
    ¬∃ d : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.gcd a b = d

/--
**Erdős Problem #535** (Upper bound conjecture):

For each $r \geq 3$, there exists a constant $c > 0$ and $N_0$ such that for all
$N \geq N_0$, every $r$-GCD-uniform-free subset of $\{1, \ldots, N\}$ has size
at most $N^{c / \log\log N}$.
-/
theorem erdos_problem_535_upper (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Icc 1 N → IsGCDUniformFree A r →
        (A.card : ℝ) ≤ (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) :=
  sorry

/--
**Erdős Problem #535** (Lower bound, proved by Erdős [Er64] for $r = 3$):

There exists a constant $c > 0$ and $N_0$ such that for all $N \geq N_0$,
there exists a $3$-GCD-uniform-free subset of $\{1, \ldots, N\}$ of size at
least $N^{c / \log\log N}$.
-/
theorem erdos_problem_535_lower :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ IsGCDUniformFree A 3 ∧
        (N : ℝ) ^ (c / Real.log (Real.log (N : ℝ))) ≤ (A.card : ℝ) :=
  sorry

end
