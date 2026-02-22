import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1014

Let R(k,l) be the Ramsey number, so the minimal n such that every graph on at
least n vertices contains either a K_k or an independent set on l vertices.

Prove, for fixed k ≥ 3, that
  lim_{l → ∞} R(k, l+1) / R(k, l) = 1.

This is open even for k = 3.

Tags: graph theory, ramsey theory
-/

/-- The Ramsey number R(k, l): the minimum N such that every simple graph on N
    vertices contains either a k-clique or an independent set of size l
    (equivalently, an l-clique in the complement). -/
noncomputable def ramseyR (k l : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree l}

/--
Erdős Problem #1014 [Er71, p.99]:

For fixed k ≥ 3, lim_{l → ∞} R(k, l+1) / R(k, l) = 1,

where R(k, l) is the Ramsey number.

Formulated as: for every ε > 0, there exists L₀ such that for all l ≥ L₀,
  |R(k, l+1) / R(k, l) - 1| ≤ ε.
-/
theorem erdos_problem_1014 (k : ℕ) (hk : k ≥ 3) :
    ∀ ε : ℝ, ε > 0 →
    ∃ L₀ : ℕ, ∀ l : ℕ, l ≥ L₀ →
      |(ramseyR k (l + 1) : ℝ) / (ramseyR k l : ℝ) - 1| ≤ ε :=
  sorry

end
