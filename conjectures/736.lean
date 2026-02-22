import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Aleph

open SimpleGraph Cardinal

universe u

noncomputable section

/-!
# Erdős Problem #736

Let G be a graph with chromatic number ℵ₁. Is there, for every cardinal
number m, some graph G_m of chromatic number m such that every finite
subgraph of G_m is a subgraph of G?

A conjecture of Walter Taylor. The more general problem replaces ℵ₁ with
any uncountable cardinal κ.

Komjáth and Shelah [KoSh05] proved that it is consistent that the answer
is no, so the conjecture is not provable in ZFC.

https://www.erdosproblems.com/736
-/

/-- G contains a copy of H: there is an injective map preserving adjacency. -/
def SimpleGraph.ContainsCopy {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- The cardinal chromatic number of a graph: the infimum of cardinals κ
    for which G admits a proper κ-coloring. -/
noncomputable def SimpleGraph.cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem #736 [Er81] [Er93,p.343]:

If G is a graph with chromatic number ℵ₁, then for every cardinal m,
there exists a graph G_m with chromatic number m such that every finite
subgraph of G_m is also a subgraph of G.

A conjecture of Walter Taylor. Komjáth and Shelah [KoSh05] proved that
this is consistently false (not provable in ZFC).
-/
theorem erdos_problem_736 {V : Type u} (G : SimpleGraph V)
    (hχ : G.cardChromaticNumber = aleph 1) :
    ∀ (m : Cardinal.{u}),
    ∃ (W : Type u) (Gm : SimpleGraph W),
      Gm.cardChromaticNumber = m ∧
      ∀ (U : Type u) [Fintype U] (H : SimpleGraph U),
        Gm.ContainsCopy H → G.ContainsCopy H :=
  sorry

end
