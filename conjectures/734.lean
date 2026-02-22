import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

/-!
# Erdős Problem #734

Find, for all large $n$, a non-trivial pairwise balanced block design
$A_1, \ldots, A_m \subseteq \{1, \ldots, n\}$ such that, for all $t$,
there are $O(n^{1/2})$ many $i$ such that $|A_i| = t$.

A pairwise balanced block design (PBBD) on $\{1, \ldots, n\}$ is a
collection of subsets such that every pair of distinct elements is
contained in exactly one block.

Erdős and de Bruijn proved that any PBBD has $m \geq n$ blocks, which
implies there must be some block size $t$ appearing at least
$\Omega(\sqrt{n})$ times. This conjecture asks whether $O(\sqrt{n})$ is
achievable for every block size simultaneously.
-/

/-- A pairwise balanced block design (PBBD) on `Fin n`: a collection of
    subsets such that every pair of distinct elements is contained in
    exactly one block. -/
def IsPBBD (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  ∀ (a b : Fin n), a ≠ b →
    (blocks.filter (fun B => a ∈ B ∧ b ∈ B)).card = 1

/--
Erdős Problem #734 [Er81, p.35]:

For all sufficiently large n, there exists a non-trivial pairwise balanced
block design on {1, ..., n} where for every t, at most O(√n) blocks have
size t. Non-trivial means at least one block has size ≥ 3.
-/
theorem erdos_problem_734 :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ blocks : Finset (Finset (Fin n)),
        IsPBBD n blocks ∧
        (∃ B ∈ blocks, 2 < B.card) ∧
        ∀ t : ℕ, ((blocks.filter (fun B => B.card = t)).card : ℝ) ≤
          C * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry
