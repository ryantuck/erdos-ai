import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open SimpleGraph Cardinal

universe u

noncomputable section

/-!
# Erdős Problem #740

Let 𝔪 be an infinite cardinal and G be a graph with chromatic number 𝔪.
Let r ≥ 1. Must G contain a subgraph of chromatic number 𝔪 which does not
contain any odd cycle of length ≤ r?

A question of Erdős and Hajnal [Er69b][Er71,p.100][Er81][Er95d].
Rödl proved this is true if 𝔪 = ℵ₀ and r = 3 (see [108] for the finitary
version).

More generally, Erdős and Hajnal asked whether for every cardinal 𝔪 and
integer r, there exists f_r(𝔪) such that every graph with chromatic number
≥ f_r(𝔪) contains a subgraph with chromatic number 𝔪 with no odd cycle
of length ≤ r.

https://www.erdosproblems.com/740
-/

/-- The cardinal chromatic number of a graph: the infimum of cardinals κ
    for which G admits a proper κ-coloring. -/
noncomputable def SimpleGraph.cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem #740 [Er69b][Er71][Er81][Er95d]:

If G is a graph with infinite chromatic number 𝔪, then for every r ≥ 1,
G contains a subgraph with chromatic number 𝔪 that has no odd cycle of
length ≤ r.

A question of Erdős and Hajnal. Rödl proved the case 𝔪 = ℵ₀, r = 3.
-/
theorem erdos_problem_740 {V : Type u} (G : SimpleGraph V)
    (𝔪 : Cardinal.{u}) (h𝔪_inf : ℵ₀ ≤ 𝔪)
    (hχ : G.cardChromaticNumber = 𝔪) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (W : Type u) (H : SimpleGraph W),
      H.cardChromaticNumber = 𝔪 ∧
      (∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ (w : W) (p : H.Walk w w), p.IsCycle → Odd p.length → r < p.length) :=
  sorry

end
