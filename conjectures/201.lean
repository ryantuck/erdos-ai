import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #201

Let $G_k(N)$ be such that any set of $N$ integers contains a subset of
size at least $G_k(N)$ which does not contain a $k$-term arithmetic
progression. Let $R_k(N)$ be the size of the largest subset of
$\{1,\ldots,N\}$ without a $k$-term arithmetic progression.

Is it true that $\lim_{N\to\infty} R_3(N)/G_3(N) = 1$?

It is trivial that $G_k(N) \leq R_k(N)$. Komlós, Sulyok, and Szemerédi
[KSS75] showed that $R_k(N) \ll_k G_k(N)$.
-/

noncomputable section
open Classical

/-- A finset of integers contains a k-term arithmetic progression if there
    exist integers a, d with d ≠ 0 such that a + i·d ∈ S for all 0 ≤ i < k. -/
def HasKTermAP (k : ℕ) (S : Finset ℤ) : Prop :=
  ∃ a d : ℤ, d ≠ 0 ∧ ∀ i : Fin k, (a + (i.val : ℤ) * d) ∈ S

/-- The maximum cardinality of a subset of S that contains no k-term AP. -/
def maxAPFreeSize (k : ℕ) (S : Finset ℤ) : ℕ :=
  Finset.sup (S.powerset.filter (fun T => ¬HasKTermAP k T)) Finset.card

/-- R_k(N): the size of the largest subset of {1,...,N} without a k-term AP. -/
def R_ap (k N : ℕ) : ℕ :=
  maxAPFreeSize k (Finset.Icc (1 : ℤ) (N : ℤ))

/--
Erdős Problem #201 [Er73, Er75b, ErGr79, ErGr80]:

Is it true that lim_{N→∞} R_3(N) / G_3(N) = 1?

Since G_k(N) ≤ R_k(N) always holds, the conjecture is equivalent to:
for every ε > 0, for all sufficiently large N, every set of N integers
contains a 3-AP-free subset of size at least (1 - ε) · R_3(N).
-/
theorem erdos_problem_201 :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, S.card = N →
        ∃ T ⊆ S, ¬HasKTermAP 3 T ∧
          (1 - ε) * (R_ap 3 N : ℝ) ≤ (T.card : ℝ) := by
  sorry

end
