import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real Classical

/-!
Erdős Problem #797 [AlBe76] (Proved):

Let f(d) be the maximal acyclic chromatic number of any graph with maximum
degree d — that is, the vertices of any graph with maximum degree d can be
coloured with f(d) colours such that there is no edge between vertices of the
same colour and no cycle containing only two colours.

Estimate f(d). In particular is it true that f(d) = o(d²)?

The trivial greedy bound gives f(d) ≤ d² + 1. Erdős showed f(d) ≥ d^{4/3-o(1)}.

Resolved by Alon, McDiarmid, and Reed [AMR91] who showed
  d^{4/3} / (log d)^{1/3} ≪ f(d) ≪ d^{4/3}.
-/

/-- A proper coloring of G is acyclic if for every pair of distinct colors,
    the subgraph induced by vertices of those two colors is acyclic (a forest). -/
def IsAcyclicColoring {V : Type*} (G : SimpleGraph V) {α : Type*}
    (c : G.Coloring α) : Prop :=
  ∀ a b : α, a ≠ b →
    (G.induce {v : V | c v = a ∨ c v = b}).IsAcyclic

theorem erdos_problem_797 :
    -- Upper bound: f(d) ≪ d^{4/3}
    (∃ C : ℝ, 0 < C ∧
      ∀ (d n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ v, G.degree v ≤ d) →
        ∃ (k : ℕ) (c : G.Coloring (Fin k)),
          IsAcyclicColoring G c ∧ (k : ℝ) ≤ C * (d : ℝ) ^ ((4 : ℝ) / 3)) ∧
    -- Lower bound: f(d) ≫ d^{4/3} / (log d)^{1/3}
    (∃ C : ℝ, 0 < C ∧
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          (∀ v, G.degree v ≤ d) ∧
          ∀ (k : ℕ), (∃ c : G.Coloring (Fin k), IsAcyclicColoring G c) →
            C * (d : ℝ) ^ ((4 : ℝ) / 3) / (Real.log (d : ℝ)) ^ ((1 : ℝ) / 3) ≤ (k : ℝ)) :=
  sorry
