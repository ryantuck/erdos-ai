import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

open Finset SimpleGraph

example (n : ℕ) (G : SimpleGraph (Fin n)) (h : DecidableRel G.Adj) : Finset (Sym2 (Fin n)) :=
  have : DecidableRel G.Adj := h
  G.edgeFinset
