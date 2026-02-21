import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Real Filter

noncomputable section

/-!
# Erdős Problem #150

A minimal cut of a graph is a minimal set of vertices whose removal disconnects
the graph. Let c(n) be the maximum number of minimal cuts a graph on n vertices
can have. Does c(n)^(1/n) → α for some α < 2?

Asked by Erdős and Nešetřil. Seymour observed that c(3m+2) ≥ 3^m via m
independent paths of length 4 joining two vertices.

Proved by Bradač [Br24]: the limit α = lim c(n)^(1/n) exists and
α ≤ 2^H(1/3) = 1.8899... < 2, where H(·) is the binary entropy function.
This confirms the conjecture. Bradač conjectures the true value is α = 3^(1/3).
-/

/-- A set S of vertices is a vertex separator of G if the subgraph induced by
    the complement V \ S is not connected. -/
def IsVertexSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ¬(G.induce ((S : Set (Fin n))ᶜ)).Connected

/-- S is a minimal vertex cut of G if S is a vertex separator and no proper
    subset of S is also a vertex separator. -/
def IsMinimalVertexCut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  IsVertexSeparator G S ∧
  ∀ T : Finset (Fin n), T ⊂ S → ¬IsVertexSeparator G T

/-- The number of minimal vertex cuts of G. -/
noncomputable def numMinimalVertexCuts {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard { S : Finset (Fin n) | IsMinimalVertexCut G S }

/-- c(n) is the maximum number of minimal vertex cuts over all connected simple
    graphs on n vertices. -/
noncomputable def c (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ G : SimpleGraph (Fin n), G.Connected ∧
    numMinimalVertexCuts G = k }

/--
Erdős Problem #150 [Er88] (asked by Erdős and Nešetřil):
Let c(n) be the maximum number of minimal vertex cuts in a graph on n vertices.
Does c(n)^(1/n) → α for some α < 2?

Proved by Bradač [Br24]: the limit α = lim c(n)^(1/n) exists and
α ≤ 2^H(1/3) = 1.8899... < 2, where H(·) is the binary entropy function.
Seymour's construction gives c(3m+2) ≥ 3^m, so α ≥ 3^(1/3) ≈ 1.442.
Bradač conjectures that the true value is α = 3^(1/3).
-/
theorem erdos_problem_150 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds α) :=
  sorry

end
