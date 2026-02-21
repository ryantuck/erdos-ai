import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Finset BigOperators Filter

/-!
# Erdős Problem #393

Let f(n) denote the minimal m ≥ 1 such that n! = a₁⋯aₜ with a₁ < ⋯ < aₜ = a₁ + m.
What is the behaviour of f(n)?

Erdős and Graham write that they do not even know whether f(n) = 1 infinitely often
(i.e. whether a factorial is the product of consecutive integers infinitely often).

A result of Luca implies that f(n) → ∞ as n → ∞, conditional on the ABC conjecture.
-/

/-- A factorization of `n!` as a product of distinct positive integers whose
    maximum minus minimum equals `m`. Concretely, there is a finite set of
    positive integers all contained in `[a, a + m]` (with both `a` and `a + m`
    achieved) whose product is `n!`. -/
def HasFactorizationWithSpread (n m : ℕ) : Prop :=
  ∃ (s : Finset ℕ),
    2 ≤ s.card ∧
    (∀ x ∈ s, 0 < x) ∧
    s.prod id = n.factorial ∧
    ∃ a ∈ s, a + m ∈ s ∧ ∀ x ∈ s, a ≤ x ∧ x ≤ a + m

/-- `erdos393_f n` is the minimal `m ≥ 1` such that `n!` can be written as a product
    of distinct positive integers spanning a range of exactly `m`. Returns `0` if no
    such factorization exists (e.g. for `n ≤ 1`). -/
noncomputable def erdos393_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ HasFactorizationWithSpread n m}

/--
Erdős Problem #393 [ErGr80, p.76]:

f(n) → ∞ as n → ∞, where f(n) is the minimum spread of any factorization of n!
into distinct positive integers. Implied by the ABC conjecture via a result of Luca.
-/
theorem erdos_problem_393 :
    Tendsto (fun n : ℕ => erdos393_f n) atTop atTop :=
  sorry
