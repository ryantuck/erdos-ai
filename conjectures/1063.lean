import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/--
For given n and k, count how many 0 ≤ i < k satisfy (n - i) ∣ C(n, k).

Intended for use with 2k ≤ n, where every n - i (0 ≤ i < k) is a genuine
positive difference. (For i ≥ n the ℕ-subtraction n - i truncates to 0, and
0 ∣ C(n, k) holds only when C(n, k) = 0; no such n occurs in the uses below.)
-/
def countDivisors (n k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun i => (n - i) ∣ Nat.choose n k)).card

/--
n_k is the least n ≥ 2k such that exactly k-1 of the values n-i (for 0 ≤ i < k)
divide C(n,k), i.e., all but one divide C(n,k). By Erdős–Selfridge
(`erdos_problem_1063_selfridge`), for k ≥ 2 and n ≥ 2k at least one of the k
values always fails to divide, so "exactly k - 1" is equivalent to the source's
"all but one".

Degenerate cases: for k = 1 the defining set is empty (n - 0 = n always divides
C(n, 1) = n, so countDivisors n 1 = 1 ≠ 0) and `sInf ∅ = 0` is a junk value; for
k = 0 every n qualifies (both sides are 0) and the value is 0. All theorems
below assume k ≥ 2, where the set is nonempty (n = 4 works for k = 2, and
n = k! works for k ≥ 3 by Monier's observation).
-/
noncomputable def erdos1063_nk (k : ℕ) : ℕ :=
  sInf {n | 2 * k ≤ n ∧ countDivisors n k = k - 1}

/--
Erdős Problem #1063 [ErSe83]:

Let k ≥ 2 and define n_k ≥ 2k to be the least value of n such that n - i divides
C(n, k) for all but one 0 ≤ i < k. Estimate n_k.

The problem is OPEN (erdosproblems.com/1063, page edition 01 February 2026,
accessed 2026-03-06). "Estimate n_k" is not directly formalizable; this theorem
states the simplest known upper bound, observed by Monier [Mo85]:
n_k ≤ k! for k ≥ 3, since C(k!, k) is divisible by k! - i for 1 ≤ i < k.
The hypothesis 3 ≤ k is necessary: n_2 = 4 > 2 = 2!.

Erdős and Selfridge noted (and a proof can be found in [Mo85]) that if n ≥ 2k
then there must exist at least one 0 ≤ i < k such that (n - i) does not divide
C(n, k); see `erdos_problem_1063_selfridge`.

Known values: n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; see
`erdos_problem_1063_small_values`.

Cambie observes (in the comments on the problem page) that Monier's bound can be
improved to n_k ≤ k · lcm(2, 3, ..., k-1) ≤ e^{(1+o(1))k}. (Not formalized here:
it would require `Finset.lcm`, a construct not otherwise used in this file.)

This is discussed in problem B31 of Guy's collection [Gu04]. Related OEIS
sequence: A389360. An upstream formalization exists at
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1063.lean.

References:
[ErSe83] Erdős, P. and Selfridge, J. L. (1983). Problem source; full
bibliographic data not recoverable offline.
[Mo85] Monier (1985). Full bibliographic data not recoverable offline.
[Gu04] Guy, R. K., *Unsolved problems in number theory*, 3rd ed., Springer
(2004), Problem B31.
-/
theorem erdos_problem_1063 (k : ℕ) (hk : 3 ≤ k) :
    erdos1063_nk k ≤ k.factorial :=
  sorry

/--
Erdős and Selfridge [ErSe83] noted (a proof can be found in [Mo85]) that if
n ≥ 2k, with k ≥ 2, then at least one 0 ≤ i < k satisfies (n - i) ∤ C(n, k) —
that is, fewer than k of the k values n - i divide C(n, k). Hence "all but one"
in the definition of n_k means exactly k - 1.
-/
theorem erdos_problem_1063_selfridge (k n : ℕ) (hk : 2 ≤ k) (hn : 2 * k ≤ n) :
    countDivisors n k < k :=
  sorry

/--
The known small values of n_k: n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12
(erdosproblems.com/1063). Each is verified by hand against the definition,
e.g. n_4 = 9: C(9, 4) = 126 is divisible by 9, 7, 6 but not 8, while
n = 8 gives C(8, 4) = 70, divisible only by 7 and 5.
-/
theorem erdos_problem_1063_small_values :
    erdos1063_nk 2 = 4 ∧ erdos1063_nk 3 = 6 ∧ erdos1063_nk 4 = 9 ∧
      erdos1063_nk 5 = 12 :=
  sorry
