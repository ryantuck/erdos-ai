import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1030

If R(k,l) is the Ramsey number then prove the existence of some c > 0 such that
  lim_{k → ∞} R(k+1, k) / R(k, k) > 1 + c.

A problem of Erdős and Sós, who could not even prove whether R(k+1,k) - R(k,k) > k^c
for any c > 1.

Tags: graph theory, ramsey theory
-/

/-- The Ramsey number R(k, l): the minimum N such that every simple graph on N
    vertices contains either a k-clique or an independent set of size l
    (equivalently, an l-clique in the complement). -/
noncomputable def ramseyR (k l : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree l}

/--
Erdős Problem #1030 [Er93, p.339]:

There exists c > 0 such that lim_{k → ∞} R(k+1, k) / R(k, k) > 1 + c.

Formulated as: there exist c > 0 and K₀ such that for all k ≥ K₀,
  R(k+1, k) / R(k, k) ≥ 1 + c.
-/
theorem erdos_problem_1030 :
    ∃ c : ℝ, c > 0 ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (ramseyR (k + 1) k : ℝ) / (ramseyR k k : ℝ) ≥ 1 + c :=
  sorry

end
