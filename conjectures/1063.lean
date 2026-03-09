import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/--
For given n and k, count how many 0 ≤ i < k satisfy (n - i) ∣ C(n, k).
-/
def countDivisors (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => (n - i) ∣ Nat.choose n k)).card

/--
n_k is the least n ≥ 2k such that exactly k-1 of the values n-i (for 0 ≤ i < k)
divide C(n,k), i.e., all but one divide C(n,k).
-/
noncomputable def erdos1063_nk (k : ℕ) : ℕ :=
  Nat.find (⟨k.factorial, sorry⟩ : ∃ n, 2 * k ≤ n ∧ countDivisors n k = k - 1)

/--
Erdős Problem #1063 [ErSe83]:

Let k ≥ 2 and define n_k ≥ 2k to be the least value of n such that n - i divides
C(n, k) for all but one 0 ≤ i < k. Estimate n_k.

Erdős and Selfridge noted that if n ≥ 2k then there must exist at least one
0 ≤ i < k such that (n - i) does not divide C(n, k).

Known values: n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12.

Monier observed that n_k ≤ k! for k ≥ 3. Cambie improved this to
n_k ≤ k · lcm(2, 3, ..., k-1) ≤ e^{(1+o(1))k}.
-/
theorem erdos_problem_1063 (k : ℕ) (hk : 2 ≤ k) :
    erdos1063_nk k ≤ k.factorial :=
  sorry
