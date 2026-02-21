import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

open Finset

/-!
# Erdős Problem #430

Fix an integer n and define a decreasing sequence by a₁ = n-1 and, for k ≥ 2,
aₖ is the greatest integer m in [2, aₖ₋₁) such that all prime factors of m
are > n - m. The sequence terminates when no such m exists.

Conjecture: for sufficiently large n, not all terms of the sequence are prime.

Erdős and Graham write 'preliminary calculations made by Selfridge indicate
that this is the case but no proof is in sight'. For example if n = 8 we have
a₁ = 7 and a₂ = 5 and then the sequence terminates.
-/

/-- The next term in the Erdős 430 sequence: the greatest m in [2, prev) such that
    all prime factors of m are > n - m. The condition "all prime factors > n - m"
    is equivalent to minFac m > n - m, i.e., n < m + minFac m.
    Returns 0 if no such m exists (sequence terminates). -/
def erdos430_next (n prev : ℕ) : ℕ :=
  let S := (Ico 2 prev).filter (fun m => n < m + m.minFac)
  if h : S.Nonempty then S.max' h else 0

/-- The Erdős 430 sequence for a given n: a(0) = n - 1,
    a(k+1) = erdos430_next n (a(k)). Terms become 0 once the sequence terminates. -/
def erdos430_seq (n : ℕ) : ℕ → ℕ
  | 0 => n - 1
  | k + 1 => erdos430_next n (erdos430_seq n k)

/--
Erdős Problem #430 [ErGr80]:

For sufficiently large n, the greedy decreasing sequence in [2, n) starting at
n - 1, where each term has all prime factors larger than its complement to n,
must contain a composite number.
-/
theorem erdos_problem_430 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ k : ℕ, 2 ≤ erdos430_seq n k ∧ ¬(erdos430_seq n k).Prime :=
  sorry
