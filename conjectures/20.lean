import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

/--
A family `F` of finite sets is **n-uniform** if every member has cardinality `n`.
-/
def NUniform {α : Type*} (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ S ∈ F, Finset.card S = n

/--
A **k-sunflower** (or Δ-system of size k) in a family of sets is a subfamily
of `k` sets such that every pair shares the same intersection (the "core").
Equivalently, there exists a core `C` such that for any two distinct members
`S₁, S₂` of the subfamily, `S₁ ∩ S₂ = C`.
-/
def IsSunflower {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (k : ℕ) : Prop :=
  Finset.card G = k ∧
    ∃ C : Finset α, ∀ S₁ ∈ G, ∀ S₂ ∈ G, S₁ ≠ S₂ → S₁ ∩ S₂ = C

/--
Erdős Problem #20 [Er65b, Er69, Er71, Er73, Er81, Er90, Er95, Er97c, Er97d]:

Let f(n,k) be minimal such that every family F of n-uniform sets with
|F| ≥ f(n,k) contains a k-sunflower. Is it true that f(n,k) < c_k^n
for some constant c_k > 0?

This is the Sunflower conjecture of Erdős and Rado. The best known bound is
f(n,k) < (C k log n)^n for some constant C > 1, due to Alweiss, Lovett, Wu,
and Zhang (2020), later refined by Rao and others. Erdős offered $1000 for
a proof or disproof even in the case k = 3.
-/
theorem erdos_problem_20 :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c : ℝ, 0 < c ∧
        ∀ (α : Type*) [DecidableEq α] (n : ℕ) (F : Finset (Finset α)),
          NUniform F n →
          (Finset.card F : ℝ) ≥ c ^ n →
          ∃ G : Finset (Finset α), G ⊆ F ∧ IsSunflower G k :=
  sorry
