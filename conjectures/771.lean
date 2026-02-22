import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Real

noncomputable section

/-!
# Erdős Problem #771

Let f(n) be maximal such that, for every m ≥ 1, there exists some
S ⊆ {1, …, n} with |S| = f(n) such that m ≠ ∑_{a ∈ A} a for all A ⊆ S.

Is it true that f(n) = (1/2 + o(1)) · n / log n?

A conjecture of Erdős and Graham (PROVED). The lower bound
f(n) ≥ (1/2 + o(1)) · n / log n was proved by Erdős and Graham, who took
S = {kp : 1 ≤ k < n/p} where p is the least prime not dividing m. The
matching upper bound was proved by Alon and Freiman [AlFr88].

https://www.erdosproblems.com/771

Tags: number theory
-/

/-- m is a subset sum of S: there exists A ⊆ S with ∑_{a ∈ A} a = m. -/
def IsSubsetSum771 (S : Finset ℕ) (m : ℕ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ S ∧ A.sum id = m

/-- f(n) is the maximum k such that for every positive integer m, there exists
    a k-element subset S ⊆ {1, …, n} for which m is not a subset sum of S. -/
noncomputable def erdos771_f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ m : ℕ, m ≥ 1 →
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ S.card = k ∧ ¬IsSubsetSum771 S m}

/--
Erdős Problem #771 (PROVED, Erdős–Graham + Alon–Freiman [AlFr88]):

f(n) = (1/2 + o(1)) · n / log n.

Formally: for every ε > 0, there exists N₀ such that for all n ≥ N₀,
  (1/2 - ε) · n / log n ≤ f(n) ≤ (1/2 + ε) · n / log n.
-/
theorem erdos_problem_771 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 / 2 - ε) * (↑n / Real.log ↑n) ≤ ↑(erdos771_f n) ∧
      ↑(erdos771_f n) ≤ (1 / 2 + ε) * (↑n / Real.log ↑n) :=
  sorry

end
