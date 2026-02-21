import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #166

Prove that R(4,k) ≫ k³/(log k)^{O(1)}.

R(4,k) is the Ramsey number: the minimum N such that every simple graph
on N vertices contains either a 4-clique or an independent set of size k
(equivalently, a k-clique in the complement).

Ajtai, Komlós, and Szemerédi [AKS80] proved the upper bound
  R(4,k) ≪ k³/(log k)².
Spencer [Sp77] proved R(4,k) ≫ (k log k)^{5/2}.
Mattheus and Verstraete [MaVe23] proved R(4,k) ≫ k³/(log k)⁴,
resolving this conjecture.
-/

/-- The Ramsey number R(4,k): the minimum N such that every simple graph
    on N vertices contains either a 4-clique or an independent set of
    size k (a k-clique in the complement). -/
noncomputable def ramseyR4 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Conjecture (Problem #166) [Er90b, Er91, Er93, Er97c]:

There exist constants C > 0 and α : ℕ such that for all sufficiently large k,
  R(4,k) ≥ C · k³ / (log k)^α.

In asymptotic notation: R(4,k) ≫ k³/(log k)^{O(1)}.

This was proved by Mattheus and Verstraete [MaVe23], who showed
  R(4,k) ≫ k³/(log k)⁴.
-/
theorem erdos_problem_166 :
    ∃ C : ℝ, 0 < C ∧
    ∃ α : ℕ,
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ) :=
  sorry

end
