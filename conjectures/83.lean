import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Finset

/--
Erdős Problem #83 (Erdős–Ko–Rado):
Suppose that we have a family F of subsets of [4n] such that |A| = 2n for all
A ∈ F and for every A, B ∈ F we have |A ∩ B| ≥ 2. Then
|F| ≤ (1/2)(C(4n, 2n) - C(2n, n)²).

This was conjectured by Erdős, Ko, and Rado, and proved by Ahlswede and
Khachatrian (1997).
-/
theorem erdos_problem_83 :
    ∀ n : ℕ, 0 < n →
    ∀ F : Finset (Finset (Fin (4 * n))),
      (∀ A ∈ F, A.card = 2 * n) →
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ 2) →
      F.card ≤ (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2 :=
  sorry
