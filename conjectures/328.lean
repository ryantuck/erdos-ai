import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Classical Finset

/-- The additive representation count: the number of pairs (a, b) with a + b = n
    and both a, b in A. This formalizes 1_A ∗ 1_A(n). -/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ (n - a) ∈ A)).card

/--
Erdős Problem #328 (DISPROVED) [ErGr80, p.48]:

Suppose A ⊆ ℕ and C > 0 is such that 1_A ∗ 1_A(n) ≤ C for all n ∈ ℕ.
Can A be partitioned into t many subsets A₁,...,Aₜ (where t = t(C) depends
only on C) such that 1_{Aᵢ} ∗ 1_{Aᵢ}(n) < C for all 1 ≤ i ≤ t and n ∈ ℕ?

Asked by Erdős and Newman. Nešetřil and Rödl [NeRo85] showed the answer is no
for all C (even if t is also allowed to depend on A).

We formalize the negation (the true statement): for every C ≥ 1, there exists
A ⊆ ℕ with representation function bounded by C, such that for every finite
partition of A, some part has representation function ≥ C at some n.
-/
theorem erdos_problem_328 :
    ∀ C : ℕ, 1 ≤ C →
      ∃ A : Set ℕ,
        (∀ n, repCount A n ≤ C) ∧
        ∀ t : ℕ, 1 ≤ t →
          ∀ f : ℕ → Fin t,
            ∃ (i : Fin t) (n : ℕ),
              repCount ({a | a ∈ A ∧ f a = i}) n ≥ C :=
  sorry
