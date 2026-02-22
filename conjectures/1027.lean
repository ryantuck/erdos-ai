import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

open Finset

/-!
# Erdős Problem #1027

Let c > 0, and let n be sufficiently large depending on c. Suppose that F is a
family of at most c·2^n many finite sets of size n. Let X = ∪_{A ∈ F} A.

Must there exist ≫_c 2^|X| many sets B ⊂ X which intersect every set in F,
yet contain none of them?

This was proved in the affirmative by Koishi Chan.
-/

/--
Erdős Problem #1027:

For every c > 0, there exist δ > 0 and N₀ such that for all n ≥ N₀,
for any family F of finite sets each of size n with |F| ≤ c · 2^n,
letting X = ∪F, the number of subsets B of X that intersect every
member of F but contain none of them is at least δ · 2^|X|.
-/
theorem erdos_problem_1027 :
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ F : Finset (Finset ℕ),
      (∀ A ∈ F, A.card = n) →
      (F.card : ℝ) ≤ c * (2 : ℝ) ^ n →
      let X := F.biUnion id
      ((X.powerset.filter (fun B =>
        (∀ A ∈ F, (A ∩ B).Nonempty) ∧
        (∀ A ∈ F, ¬(A ⊆ B)))).card : ℝ) ≥ δ * (2 : ℝ) ^ X.card :=
  sorry
