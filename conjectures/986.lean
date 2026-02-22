import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #986

For any fixed k ≥ 3, R(k,n) ≫ n^{k-1}/(log n)^c for some constant c = c(k) > 0.

R(k,n) is the Ramsey number: the minimum N such that every simple graph
on N vertices contains either a k-clique or an independent set of size n
(equivalently, an n-clique in the complement).

Spencer [Sp77] proved this for k = 3 and Mattheus and Verstraete [MaVe23]
proved this for k = 4.

The best general bounds available are:
  n^{(k+1)/2} / (log n)^{1/(k-2) - (k+1)/2} ≪_k R(k,n) ≪_k n^{k-1} / (log n)^{k-2}

The lower bound was proved by Bohman and Keevash [BoKe10].
The upper bound was proved by Ajtai, Komlós, and Szemerédi [AKS80].
-/

/-- The Ramsey number R(k,n): the minimum N such that every simple graph
    on N vertices contains either a k-clique or an independent set of
    size n (an n-clique in the complement). -/
noncomputable def ramseyR (k n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree k ∨ ¬Gᶜ.CliqueFree n}

/--
Erdős Conjecture (Problem #986) [Er90b]:

For any fixed k ≥ 3, there exist constants C > 0 and c : ℕ with c > 0
such that for all sufficiently large n:
  R(k,n) ≥ C · n^{k-1} / (log n)^c.

In asymptotic notation: R(k,n) ≫ n^{k-1}/(log n)^c for some c > 0.
-/
theorem erdos_problem_986 (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧
    ∃ c : ℕ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      C * ((n : ℝ) ^ (k - 1) / (Real.log (n : ℝ)) ^ c) ≤ (ramseyR k n : ℝ) :=
  sorry

end
