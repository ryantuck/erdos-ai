import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fin.VecNotation

open Finset Nat

noncomputable section

/-!
# Erdős Problem #1056

Let k ≥ 2. Does there exist a prime p and consecutive intervals I₁, …, I_k such that
∏_{n ∈ I_i} n ≡ 1 (mod p) for all 1 ≤ i ≤ k?

Erdős observed that 3·4 ≡ 5·6·7 ≡ 1 (mod 11), establishing the case k = 2.
Makowski found, for k = 3:
2·3·4·5 ≡ 6·7·8·9·10·11 ≡ 12·13·14·15 ≡ 1 (mod 17).
-/

/-- `AllModProdEqualsOne p boundaries` asserts that for each interval defined by
consecutive boundaries, the product of all natural numbers in that interval is
≡ 1 (mod p). The intervals are `[boundaries i, boundaries (i+1))` for each `i`. -/
def AllModProdEqualsOne (p : ℕ) {k : ℕ} (boundaries : Fin (k + 1) → ℕ) : Prop :=
  ∀ i : Fin k,
    (∏ n ∈ Finset.Ico (boundaries i.castSucc) (boundaries (i.castSucc + 1)), n) ≡ 1 [MOD p]

/--
Erdős Problem #1056 [Gu04]:

For every k ≥ 2, there exists a prime p and consecutive intervals I₁, …, I_k
(given by strictly increasing boundaries) such that the product of integers
in each interval is ≡ 1 (mod p).
-/
theorem erdos_problem_1056 :
    ∀ k : ℕ, k ≥ 2 →
    ∃ (p : ℕ) (_ : p.Prime) (boundaries : Fin (k + 1) → ℕ),
      StrictMono boundaries ∧ AllModProdEqualsOne p boundaries :=
  sorry

/-- Erdős observed in 1979 that 3·4 ≡ 5·6·7 ≡ 1 (mod 11), establishing k = 2. -/
theorem erdos_problem_1056_k2 :
    AllModProdEqualsOne 11 ![3, 5, 8] := by
  unfold AllModProdEqualsOne
  decide

/-- Makowski found for k = 3:
2·3·4·5 ≡ 6·7·8·9·10·11 ≡ 12·13·14·15 ≡ 1 (mod 17). -/
theorem erdos_problem_1056_k3 :
    AllModProdEqualsOne 17 ![2, 6, 12, 16] := by
  unfold AllModProdEqualsOne
  decide

end
