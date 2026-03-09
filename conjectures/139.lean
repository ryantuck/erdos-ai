import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

/--
A Finset S of natural numbers is free of non-trivial k-term arithmetic
progressions: there do not exist a, d with d ≥ 1 such that
{a, a+d, …, a+(k-1)d} ⊆ S.
-/
def APFree (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ∃ i : ℕ, i < k ∧ a + i * d ∉ S

/--
Erdős Problem #139 (Erdős–Turán conjecture / Szemerédi's theorem):

For every k ≥ 3 and every ε > 0, there exists N₀ such that for all N ≥ N₀,
every subset of {0, …, N-1} with no non-trivial k-term arithmetic progression
has size at most ε * N.

Equivalently, r_k(N) = o(N).

Proved by Szemerédi [Sz75].
-/
theorem erdos_problem_139
    (k : ℕ) (hk : 3 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → APFree k S →
        (S.card : ℝ) ≤ ε * (N : ℝ) :=
  sorry
