import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

/-- An injective graph homomorphism from H to G; witnesses that G contains a
    copy of H as a subgraph. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős-Füredi-Loebl-Sós Conjecture (Problem #580):
Let G be a graph on n vertices such that at least n/2 vertices have degree at
least n/2. Must G contain every tree on at most n/2 vertices?

Conjectured by Erdős, Füredi, Loebl, and Sós [EFLS95].
Ajtai, Komlós, and Szemerédi [AKS95] proved an asymptotic version.
Zhao [Zh11] proved the conjecture for all sufficiently large n.

https://www.erdosproblems.com/580
-/
theorem erdos_problem_580 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : n / 2 ≤ (Finset.univ.filter (fun v => n / 2 ≤ G.degree v)).card) :
    ∀ (k : ℕ) (T : SimpleGraph (Fin k)) [DecidableRel T.Adj],
      k ≤ n / 2 → T.IsTree → containsSubgraph G T :=
  sorry
