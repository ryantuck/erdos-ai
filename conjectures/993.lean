import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Powerset

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #993

The independent set sequence of any tree or forest is unimodal.

In other words, if i_k(G) counts the number of independent sets of vertices of
size k in a graph G, and T is any tree or forest, then for some m ≥ 0

  i_0(T) ≤ i_1(T) ≤ ⋯ ≤ i_m(T) ≥ i_{m+1}(T) ≥ i_{m+2}(T) ≥ ⋯

A question of Alavi, Malde, Schwenk, and Erdős [AMSE87], who showed that this
is false for general graphs G (in fact every possible pattern of inequalities
is achieved by some graph).
-/

/-- The number of independent sets of size `k` in a simple graph `G`.
    An independent set is a set of vertices that are pairwise non-adjacent. -/
def numIndepSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun s : Finset V =>
    s.card = k ∧ ∀ ⦃u⦄, u ∈ s → ∀ ⦃v⦄, v ∈ s → u ≠ v → ¬G.Adj u v)).card

/--
Erdős Problem #993 [AMSE87]:

The independent set sequence of any tree or forest is unimodal. That is, if
i_k(T) counts the number of independent sets of vertices of size k in a
forest T, then there exists m ≥ 0 such that

  i_0(T) ≤ i_1(T) ≤ ⋯ ≤ i_m(T) ≥ i_{m+1}(T) ≥ i_{m+2}(T) ≥ ⋯
-/
theorem erdos_problem_993 {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsAcyclic) :
    ∃ m : ℕ, (∀ i j : ℕ, i ≤ j → j ≤ m → numIndepSets T i ≤ numIndepSets T j) ∧
             (∀ i j : ℕ, m ≤ i → i ≤ j → numIndepSets T j ≤ numIndepSets T i) :=
  sorry

end
