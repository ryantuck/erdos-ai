import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/-!
# Erdős Problem #531

Let $F(k)$ be the minimal $N$ such that if we two-colour $\{1,\ldots,N\}$ there
is a set $A$ of size $k$ such that all subset sums $\sum_{a\in S}a$
(for $\emptyset\neq S\subseteq A$) are monochromatic. Estimate $F(k)$.

The existence of $F(k)$ was established by Sanders and Folkman, and also follows
from Rado's theorem. This is commonly known as Folkman's theorem.

Known lower bounds:
- Erdős–Spencer [ErSp89]: $F(k) \geq 2^{ck^2/\log k}$ for some $c > 0$.
- Balogh–Eberhard–Narayanan–Treglown–Wagner [BENTW17]: $F(k) \geq 2^{2^{k-1}/k}$.
-/

/-- A 2-coloring `χ : ℕ → Bool` admits a **monochromatic subset-sum k-set**
    within `{1, …, N}` if there is a `k`-element set `A ⊆ {1, …, N}` whose
    non-empty subset sums all lie in `{1, …, N}` and receive the same color. -/
def HasMonoSubsetSumSet (χ : ℕ → Bool) (k N : ℕ) : Prop :=
  ∃ A : Finset ℕ,
    A.card = k ∧
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    (∀ S ∈ A.powerset, S.Nonempty → ∑ i ∈ S, i ≤ N) ∧
    ∃ c : Bool, ∀ S ∈ A.powerset, S.Nonempty → χ (∑ i ∈ S, i) = c

/-- The **Folkman number** `F(k)`: the minimum `N` such that every 2-coloring
    of `{1, …, N}` admits a `k`-element subset whose non-empty subset sums
    are monochromatic. -/
noncomputable def folkmanNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → Bool, HasMonoSubsetSumSet χ k N}

/-- Folkman's theorem: for every `k`, the Folkman number `F(k)` is finite.
    That is, there exists `N` such that every 2-coloring of `{1, …, N}` has a
    monochromatic subset-sum `k`-set. -/
theorem folkman_theorem (k : ℕ) :
    ∃ N : ℕ, ∀ χ : ℕ → Bool, HasMonoSubsetSumSet χ k N :=
  sorry

/--
**Erdős Problem #531** (lower bound, [BENTW17]):

$F(k) \geq 2^{2^{k-1}/k}$ for all sufficiently large $k$.

This is the best known lower bound on the Folkman number, due to
Balogh, Eberhard, Narayanan, Treglown, and Wagner.
-/
theorem erdos_problem_531 :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (folkmanNumber k : ℝ) ≥ (2 : ℝ) ^ ((2 : ℝ) ^ ((k : ℝ) - 1) / (k : ℝ)) :=
  sorry
