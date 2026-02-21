import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Finset BigOperators Filter Classical

noncomputable section

/-!
# Erdős Problem #314

Let n ≥ 1 and let m be minimal such that ∑_{k=n}^{m} 1/k ≥ 1. Define
ε(n) = ∑_{k=n}^{m} 1/k - 1. Is it true that liminf n² ε(n) = 0?

This is true, proved by Lim and Steinerberger [LiSt24]. They further showed
that for any δ > 0, there exist infinitely many n such that
n² |∑_{k=n}^{m} 1/k - 1| ≪ 1/(log n)^{5/4 - δ}.

Erdős and Graham believe the exponent 2 is best possible, i.e.,
liminf ε(n) n^{2+δ} = ∞ for all δ > 0.
-/

/-- For any n ≥ 1, there exists m such that ∑_{k=n}^{m} 1/k ≥ 1.
    This follows from the divergence of the harmonic series. -/
lemma exists_harmonicPartialSum_ge_one (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ ∑ k ∈ Finset.Icc n m, (1 : ℝ) / (k : ℝ) := sorry

/-- m(n) is the minimal m such that ∑_{k=n}^{m} 1/k ≥ 1, for n ≥ 1.
    Returns 0 for n = 0. -/
noncomputable def erdos314_m (n : ℕ) : ℕ :=
  if h : 1 ≤ n then
    Nat.find (exists_harmonicPartialSum_ge_one n h)
  else 0

/-- ε(n) = ∑_{k=n}^{m(n)} 1/k - 1, where m(n) is minimal with ∑_{k=n}^{m(n)} 1/k ≥ 1. -/
noncomputable def erdos314_epsilon (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc n (erdos314_m n), (1 : ℝ) / (k : ℝ)) - 1

/--
Erdős Problem #314 [ErGr80, p.41] (proved by Lim–Steinerberger [LiSt24]):

Let n ≥ 1 and let m(n) be minimal such that ∑_{k=n}^{m(n)} 1/k ≥ 1.
Define ε(n) = ∑_{k=n}^{m(n)} 1/k - 1. Then liminf_{n→∞} n² ε(n) = 0.

Equivalently: for every δ > 0 and every N₀, there exists n ≥ N₀ with
n ≥ 1 such that n² ε(n) < δ.
-/
theorem erdos_problem_314 :
    ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧
      (n : ℝ) ^ 2 * erdos314_epsilon n < δ :=
  sorry

end
