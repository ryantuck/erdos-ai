import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical SimpleGraph Filter Real

noncomputable section

/-!
# Erdős Problem #134

Let ε, δ > 0 and n be sufficiently large in terms of ε and δ. Let G be a
triangle-free graph on n vertices with maximum degree < n^(1/2 - ε).

Can G be made into a triangle-free graph with diameter 2 by adding at most δn² edges?

Asked by Erdős and Gyárfás, who proved this is the case when G has maximum degree
≪ log n / log log n. A construction of Simonovits shows the conjecture fails if the
maximum degree bound is relaxed to ≤ Cn^(1/2) for a large enough constant C.

Proved in the affirmative by Alon [Al94]: a triangle-free graph on n vertices with
maximum degree < n^(1/2 - ε) can be made into a triangle-free graph with diameter 2
by adding at most O(n^(2 - ε)) edges.
-/

/-- A graph has diameter at most 2 if every pair of distinct vertices is
    either adjacent or shares a common neighbor. -/
def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/--
Erdős Problem #134 [Er97b] (proved by Alon [Al94]):

For every ε, δ > 0 and all sufficiently large n, every triangle-free graph on
n vertices with maximum degree < n^(1/2 - ε) can be extended to a triangle-free
graph with diameter ≤ 2 by adding at most δn² edges.
-/
theorem erdos134 :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ δ * (n : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #134 (Alon's strong form [Al94]):

For every ε > 0 there exists C > 0 such that for all sufficiently large n,
every triangle-free graph on n vertices with maximum degree < n^(1/2 - ε)
can be extended to a triangle-free graph with diameter ≤ 2 by adding at
most C · n^(2 - ε) edges.
-/
theorem erdos134_alon :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (2 - ε) :=
  sorry

end
