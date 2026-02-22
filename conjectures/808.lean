import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #808

Let c, ε > 0 and n be sufficiently large. If A ⊂ ℕ has |A| = n and G is any
graph on A with at least n^{1+c} edges then
  max(|A +_G A|, |A ·_G A|) ≥ |A|^{1+c-ε}
where A +_G A = {a + b : (a,b) ∈ G} and similarly for A ·_G A.

This conjecture was disproved by Alon, Ruzsa, and Solymosi [ARS20].

References: [Er77c], [ErSz83], [Er91], [Er97]
-/

/-- The graph-restricted sumset: {f(i) + f(j) : G.Adj i j}. -/
def graphSumset808 {n : ℕ} (f : Fin n → ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image
    (fun p => f p.1 + f p.2)

/-- The graph-restricted product set: {f(i) * f(j) : G.Adj i j}. -/
def graphProdset808 {n : ℕ} (f : Fin n → ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : Finset ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2)).image
    (fun p => f p.1 * f p.2)

/--
Erdős Problem #808 (disproved) [Er77c], [ErSz83], [Er91], [Er97]:

For all c, ε > 0, for sufficiently large n, if A ⊂ ℕ has |A| = n and G is
any graph on A with at least n^{1+c} edges then
  max(|A +_G A|, |A ·_G A|) ≥ n^{1+c-ε}.

Disproved by Alon, Ruzsa, and Solymosi [ARS20].
-/
theorem erdos_problem_808 (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (f : Fin n → ℕ), Function.Injective f →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (n : ℝ) ^ (1 + c) ≤ (G.edgeFinset.card : ℝ) →
    (n : ℝ) ^ (1 + c - ε) ≤
      max ((graphSumset808 f G).card : ℝ) ((graphProdset808 f G).card : ℝ) :=
  sorry

end
