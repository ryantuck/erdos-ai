import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #914

Let r ≥ 2 and m ≥ 1. Every graph with r·m vertices and minimum degree at
least m·(r-1) contains m vertex disjoint copies of K_r.

When r = 2 this follows from Dirac's theorem. Corrádi and Hajnal proved
this when r = 3. Hajnal and Szemerédi proved this for all r ≥ 4.

This is known as the Hajnal–Szemerédi theorem.

https://www.erdosproblems.com/914

Tags: graph theory
-/

/--
Erdős Problem #914 (proved by Hajnal and Szemerédi [HaSz70]):

Let r ≥ 2 and m ≥ 1. Every graph on r·m vertices with minimum degree at
least m·(r-1) contains m vertex-disjoint copies of K_r (complete graphs
on r vertices).
-/
theorem erdos_problem_914 (r m : ℕ) (hr : r ≥ 2) (hm : m ≥ 1)
    (G : SimpleGraph (Fin (r * m))) [DecidableRel G.Adj]
    (hdeg : ∀ v : Fin (r * m), G.degree v ≥ m * (r - 1)) :
    ∃ S : Fin m → Finset (Fin (r * m)),
      (∀ i, (S i).card = r) ∧
      (∀ i, G.IsClique (S i : Set (Fin (r * m)))) ∧
      (∀ i j, i ≠ j → Disjoint (S i) (S j)) :=
  sorry

end
