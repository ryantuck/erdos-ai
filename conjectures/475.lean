import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators

/--
The partial sum of a sequence f at index m: the sum f(0) + f(1) + ... + f(m).
-/
noncomputable def partialSum {n : ℕ} {α : Type*} [AddCommMonoid α]
    (f : Fin n → α) (m : Fin n) : α :=
  (univ.filter (fun i : Fin n => i ≤ m)).sum f

/--
Erdős-Graham Conjecture on sequenceable sets in 𝔽_p (Problem #475):
Let p be a prime. Given any finite set A ⊆ 𝔽_p \ {0}, there always exists
a rearrangement A = {a₁, ..., aₜ} such that all partial sums
∑_{1 ≤ k ≤ m} aₖ are distinct, for all 1 ≤ m ≤ t.

Such an ordering is called a "valid ordering" or "sequencing" of A.
Graham proved the case t = p - 1.
-/
theorem erdos_problem_475 (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p))
    (hA : ∀ a ∈ A, a ≠ 0) :
    ∃ f : Fin A.card → ZMod p,
      (∀ i, f i ∈ A) ∧
      Function.Injective f ∧
      Function.Injective (partialSum f) :=
sorry
