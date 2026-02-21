import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

/-!
# Erdős Problem #322

Let `k ≥ 3` and let `A` be the set of `k`-th powers. Define `1_A^{(k)}(n)` as
the number of representations of `n` as the sum of `k` many `k`-th powers,
i.e., the number of tuples `(a₁, …, aₖ) ∈ ℕᵏ` with `a₁ᵏ + ⋯ + aₖᵏ = n`.

The conjecture asks: for each `k ≥ 3`, does there exist some `c > 0` and
infinitely many `n` such that `1_A^{(k)}(n) > n^c`?

Connected to Waring's problem. The famous Hypothesis K of Hardy and Littlewood
asserted `1_A^{(k)}(n) ≤ n^{o(1)}`, which was disproved by Mahler for `k = 3`,
who showed `1_A^{(3)}(n) ≫ n^{1/12}` for infinitely many `n`. Erdős believed
Hypothesis K fails for all `k ≥ 4`, but this remains unknown.
-/

/-- The number of representations of `n` as a sum of `k` many `k`-th powers of
natural numbers: `|{(a₁, …, aₖ) ∈ ℕᵏ : a₁ᵏ + ⋯ + aₖᵏ = n}|`.
Each component `aᵢ` is bounded by `n` since `aᵢᵏ ≤ n` for `k ≥ 1`. -/
noncomputable def kthPowerReps (k n : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : Fin k → Fin (n + 1) =>
    (∑ i, (f i : ℕ) ^ k) = n)).card

/--
**Erdős Problem #322**: For every `k ≥ 3`, there exists `c > 0` such that
the number of representations of `n` as a sum of `k` many `k`-th powers
exceeds `n^c` for infinitely many `n`.
-/
theorem erdos_problem_322 :
    ∀ k : ℕ, 3 ≤ k →
      ∃ c : ℝ, 0 < c ∧
        ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (kthPowerReps k n : ℝ) > (n : ℝ) ^ c :=
  sorry
