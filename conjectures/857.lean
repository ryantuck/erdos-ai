import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Finset Real

/-!
# Erdős Problem #857

Let $m = m(n, k)$ be the minimal number such that in any collection of
sets $A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ there must exist a
sunflower of size $k$ — that is, some collection of $k$ of the $A_i$
which pairwise have the same intersection.

Estimate $m(n,k)$, or even better, give an asymptotic formula.

This is sometimes known as the weak sunflower problem (see problem #20
for the strong sunflower problem).

When $k = 3$, Naslund and Sawin [NaSa17] proved that
  $m(n, 3) \leq (3 / 2^{2/3})^{(1 + o(1)) n}$.

https://www.erdosproblems.com/857

Tags: combinatorics
-/

/-- A family of sets forms a sunflower if every pair of distinct members
    has the same intersection (the "kernel"). -/
def IsSunflower857 {n : ℕ} (S : Finset (Finset (Fin n))) : Prop :=
  ∃ K : Finset (Fin n), ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

/--
**Erdős Problem #857** — Weak Sunflower Problem:

For every k ≥ 2, there exists a constant c depending only on k (with c < 2)
such that any family of distinct subsets of Fin n of size greater than
c^n must contain a sunflower of size k.

The trivial upper bound on m(n,k) is 2^n (the total number of subsets),
so the content of this conjecture is that the base of the exponential
is strictly less than 2.
-/
theorem erdos_problem_857_conjecture (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℝ, 0 < c ∧ c < 2 ∧
    ∀ n : ℕ,
    ∀ F : Finset (Finset (Fin n)),
      (F.card : ℝ) > c ^ n →
      ∃ S ⊆ F, S.card = k ∧ IsSunflower857 S :=
  sorry

/--
**Erdős Problem #857** — Naslund-Sawin bound [NaSa17]:

m(n, 3) ≤ (3 / 2^(2/3))^((1 + o(1)) n).

For every ε > 0, for all sufficiently large n, any family of more than
((3 / 2^(2/3)) + ε)^n distinct subsets of Fin n contains a 3-sunflower.
-/
theorem erdos_problem_857_naslund_sawin :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ F : Finset (Finset (Fin n)),
      (F.card : ℝ) > (3 / (2 : ℝ) ^ ((2 : ℝ) / 3) + ε) ^ n →
      ∃ S ⊆ F, S.card = 3 ∧ IsSunflower857 S :=
  sorry

end
