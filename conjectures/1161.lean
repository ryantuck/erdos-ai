import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

open Finset Equiv

noncomputable section

/-!
# Erdős Problem #1161

Let $f_k(n)$ count the number of elements of $S_n$ (the symmetric group) of
order $k$. For which values of $k$ will $f_k(n)$ be maximal?

Beker [Be25d] proved that
  max_{k ≥ 1} f_k(n) ~ (n-1)!,
and characterized the maximizing values of k: for all large n,
f_k(n) = (n-1)! if and only if k ≥ 1 is minimal such that lcm(1,...,n-k) ∣ k.
-/

/-- f_k(n): the number of permutations in S_n whose order equals k. -/
noncomputable def countPermsOfOrder (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => orderOf σ = k)).card

/--
Erdős Problem #1161 (Solved by Beker [Be25d]):

Let f_k(n) count the number of elements of S_n of order k. Beker proved that
max_{k ≥ 1} f_k(n) ~ (n-1)!, i.e., the maximum over k of the number of
permutations of order k is asymptotic to (n-1)!.

Formalized as: for every ε > 0, for all sufficiently large n,
(1) there exists k ≥ 1 with f_k(n) ≥ (1 - ε) · (n-1)!, and
(2) for all k, f_k(n) ≤ (1 + ε) · (n-1)!.
-/
theorem erdos_problem_1161 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (∃ k : ℕ, k ≥ 1 ∧
          (countPermsOfOrder n k : ℝ) ≥ (1 - ε) * ((n - 1).factorial : ℝ)) ∧
        (∀ k : ℕ,
          (countPermsOfOrder n k : ℝ) ≤ (1 + ε) * ((n - 1).factorial : ℝ)) :=
  sorry

end
