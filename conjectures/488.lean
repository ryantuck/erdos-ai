import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Max

open Finset

/--
Erdős Problem #488 [Er61,p.236][Er66,p.150]:

Let A be a finite set of positive integers and
  B = { n ≥ 1 : a ∣ n for some a ∈ A }.
Is it true that, for every m > n ≥ max A,
  |B ∩ [1,m]| / m < 2 · |B ∩ [1,n]| / n ?

The constant 2 would be best possible, as witnessed by A = {a}, n = 2a-1, m = 2a.
-/
theorem erdos_problem_488
    (A : Finset ℕ)
    (hA : A.Nonempty)
    (hApos : ∀ a ∈ A, 0 < a)
    (B : ℕ → Finset ℕ :=
      fun N => (Icc 1 N).filter (fun n => ∃ a ∈ A, a ∣ n)) :
    ∀ m n : ℕ, A.max' hA ≤ n → n < m →
      (B m).card * n < 2 * (B n).card * m :=
  sorry
