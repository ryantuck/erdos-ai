import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #628

Let G be a graph with chromatic number k containing no K_k. If a, b ≥ 2 and
a + b = k + 1 then must there exist two disjoint subgraphs of G with chromatic
numbers ≥ a and ≥ b respectively?

This property is sometimes called being (a,b)-splittable. Also known as the
Erdős-Lovász Tihany conjecture [Er68b].
-/

/--
Erdős Problem #628 (Erdős-Lovász Tihany Conjecture) [Er68b]:

Let G be a graph with chromatic number k containing no complete graph K_k.
If a, b ≥ 2 and a + b = k + 1, then there exist two vertex-disjoint induced
subgraphs of G with chromatic numbers ≥ a and ≥ b respectively.
-/
theorem erdos_problem_628 {V : Type*} (G : SimpleGraph V)
    (k : ℕ) (hk : G.chromaticNumber = k)
    (hclique : G.CliqueFree k)
    (a b : ℕ) (ha : a ≥ 2) (hb : b ≥ 2) (hab : a + b = k + 1) :
    ∃ (S T : Set V), Disjoint S T ∧
      (G.induce S).chromaticNumber ≥ a ∧
      (G.induce T).chromaticNumber ≥ b :=
  sorry

end
