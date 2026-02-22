import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #796

Let k ≥ 2 and let g_k(n) be the largest possible size of A ⊆ {1, ..., n} such
that every m has < k representations as m = a₁ · a₂ with a₁ < a₂, a₁ a₂ ∈ A.

Is it true that
  g₃(n) = (n · log(log n)) / log n + (c + o(1)) · n / log n
for some constant c?
-/

/-- The number of representations of m as a₁ · a₂ with a₁ < a₂ and a₁, a₂ ∈ A.
    For each a₁ ∈ A, we check whether m / a₁ ∈ A, a₁ < m / a₁, and a₁ divides m
    (verified by a₁ * (m / a₁) = m). -/
def productRepCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a₁ => m / a₁ ∈ A ∧ a₁ < m / a₁ ∧ a₁ * (m / a₁) = m)).card

/-- g_k(n): the largest cardinality of A ⊆ {1, ..., n} such that every m has
    fewer than k representations as a₁ · a₂ with a₁ < a₂, a₁ a₂ ∈ A. -/
noncomputable def multiplicativeBkMax (k n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    (∀ m, productRepCount A m < k) ∧ A.card = s}

/--
Erdős Problem #796 [Er69, p.80]:

There exists a constant c such that
  g₃(n) = (n · log(log n)) / log n + (c + o(1)) · n / log n.

Formulated as: there exists c such that for every ε > 0, there exists N₀
such that for all n ≥ N₀,
  |g₃(n) - n · log(log n) / log n - c · n / log n| ≤ ε · n / log n.
-/
theorem erdos_problem_796 :
    ∃ c : ℝ, ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |(multiplicativeBkMax 3 n : ℝ) -
        (n : ℝ) * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) -
        c * (n : ℝ) / Real.log (n : ℝ)| ≤
      ε * (n : ℝ) / Real.log (n : ℝ) :=
  sorry

end
