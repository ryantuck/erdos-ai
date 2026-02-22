import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Aleph

open SimpleGraph Cardinal

universe u

noncomputable section

/-!
# Erdős Problem #739

Let 𝔪 be an infinite cardinal and G be a graph with chromatic number 𝔪.
Is it true that, for every infinite cardinal 𝔫 < 𝔪, there exists a subgraph
of G with chromatic number 𝔫?

A question of Galvin [Ga73], who proved this is true with 𝔪 = ℵ₀.
Komjáth [Ko88b] proved it is consistent that the answer is no
(with 𝔪 = ℵ₂ and 𝔫 = ℵ₁). Shelah [Sh90] proved that assuming V = L,
the answer is yes with 𝔪 = ℵ₂ and 𝔫 = ℵ₁.

https://www.erdosproblems.com/739
-/

/-- The cardinal chromatic number of a graph: the infimum of cardinals κ
    for which G admits a proper κ-coloring. -/
noncomputable def SimpleGraph.cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem #739 [Er81]:

If G is a graph with infinite chromatic number 𝔪, then for every infinite
cardinal 𝔫 < 𝔪, there is a subgraph of G with chromatic number 𝔫.

A question of Galvin, who proved the case 𝔪 = ℵ₀. This is not provable
in ZFC: Komjáth showed it is consistent that the answer is no.
-/
theorem erdos_problem_739 {V : Type u} (G : SimpleGraph V)
    (𝔪 : Cardinal.{u}) (h𝔪_inf : ℵ₀ ≤ 𝔪)
    (hχ : G.cardChromaticNumber = 𝔪) :
    ∀ (𝔫 : Cardinal.{u}), ℵ₀ ≤ 𝔫 → 𝔫 < 𝔪 →
    ∃ (W : Type u) (H : SimpleGraph W),
      H.cardChromaticNumber = 𝔫 ∧
      ∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b) :=
  sorry

end
