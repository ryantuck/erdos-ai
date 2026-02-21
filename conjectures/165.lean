import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #165

Give an asymptotic formula for R(3,k).

R(3,k) is the Ramsey number: the minimum N such that every simple graph
on N vertices contains either a triangle (3-clique) or an independent set
of size k (equivalently, a k-clique in the complement).

It is known that for some constant c > 0 and large k:
  (c + o(1)) k²/log k ≤ R(3,k) ≤ (1 + o(1)) k²/log k

The upper bound is due to Shearer [Sh83], improving Ajtai-Komlós-Szemerédi
[AKS80]. The lower bound constant has been improved to c ≥ 1/2 by
Hefty-Horn-King-Pfender [HHKP25]. The conjectured asymptotic is
R(3,k) ~ (1/2) k²/log k.
-/

/-- The Ramsey number R(3,k): the minimum N such that every simple graph
    on N vertices contains either a triangle (3-clique) or an independent
    set of size k (a k-clique in the complement). -/
noncomputable def ramseyR3 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Conjecture (Problem #165) [Er61, Er71, Er90b, Er93, Er97c]:

There exists a constant c > 0 such that R(3,k) ~ c · k²/log k, i.e.,
for all ε > 0 and all sufficiently large k:
  (c - ε) · k²/log k ≤ R(3,k) ≤ (c + ε) · k²/log k.

The conjectured value is c = 1/2.
-/
theorem erdos_problem_165 :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (c - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (c + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  sorry

end
