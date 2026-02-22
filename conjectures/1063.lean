import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Factorial.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #1063

Let k ≥ 2 and define n_k ≥ 2k to be the least value of n such that n - i
divides C(n, k) for all but one 0 ≤ i < k. Estimate n_k.

A problem of Erdős and Selfridge [ErSe83].

Known values: n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12.
Known bound: n_k ≤ k! for k ≥ 3 (Monier [Mo85]).
Improved: n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k} (Cambie).

The open problem is to find better estimates of n_k.

https://www.erdosproblems.com/1063
-/

/-- All but at most one of the values n - i for 0 ≤ i < k divide C(n, k).
    Formally: there exists j < k such that for all i < k with i ≠ j,
    (n - i) ∣ C(n, k). -/
def AllButOneDivBinom (n k : ℕ) : Prop :=
  ∃ j < k, ∀ i < k, i ≠ j → (n - i) ∣ Nat.choose n k

/-- n_k from Erdős Problem #1063: the least n ≥ 2k such that all but one of
    n, n-1, ..., n-k+1 divide C(n, k). Returns 0 if no such n exists. -/
noncomputable def erdos1063_nk (k : ℕ) : ℕ :=
  sInf {n : ℕ | 2 * k ≤ n ∧ AllButOneDivBinom n k}

/--
Erdős-Selfridge [ErSe83]: For n ≥ 2k and k ≥ 2, at least one of the values
n - i for 0 ≤ i < k does not divide C(n, k).
-/
theorem erdos_selfridge_1063 (n k : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ Nat.choose n k :=
  sorry

/--
Erdős Problem #1063 [ErSe83]: n_k ≤ k! for k ≥ 3 (Monier [Mo85]).

This establishes that n_k is well-defined. The open problem asks for
better estimates of n_k. The best known bound is
n_k ≤ k · lcm(2,...,k-1) ≤ e^{(1+o(1))k} due to Cambie.
-/
theorem erdos_problem_1063 (k : ℕ) (hk : 3 ≤ k) :
    erdos1063_nk k ≤ Nat.factorial k :=
  sorry

end
