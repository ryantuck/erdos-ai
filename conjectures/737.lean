import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #737

Let $G$ be a graph with chromatic number $\aleph_1$. Must there exist an
edge $e$ such that, for all large $n$, $G$ contains a cycle of length $n$
containing $e$?

A problem of Erdős, Hajnal, and Shelah [EHS74], who proved that $G$ must
contain all sufficiently large cycles (see [594]).

This is true, and was proved by Thomassen [Th83].

https://www.erdosproblems.com/737
-/

/-- A graph has uncountable chromatic number: it cannot be properly colored
    with countably many colors. -/
def HasUncountableChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- G contains a copy of the cycle graph C_m passing through edge {u, v}:
    there is an injective embedding of C_m into G that maps some edge of
    the cycle to the edge {u, v}. -/
def SimpleGraph.ContainsCycleThroughEdge {V : Type*}
    (G : SimpleGraph V) (u v : V) (m : ℕ) (hm : m ≥ 3) : Prop :=
  ∃ f : Fin m → V, Function.Injective f ∧
    (∀ a b : Fin m, (cycleGraph m hm).Adj a b → G.Adj (f a) (f b)) ∧
    ∃ a b : Fin m, (cycleGraph m hm).Adj a b ∧
      ((f a = u ∧ f b = v) ∨ (f a = v ∧ f b = u))

/--
Erdős Problem #737 [EHS74] [Er81]:

If G is a graph with chromatic number ≥ ℵ₁ (uncountable), then there
exists an edge {u, v} of G such that for all sufficiently large n,
G contains a cycle of length n passing through {u, v}.

Proved by Thomassen [Th83].
-/
theorem erdos_problem_737 {V : Type*} (G : SimpleGraph V)
    (hG : HasUncountableChromaticNumber G) :
    ∃ u v : V, G.Adj u v ∧
      ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : n ≥ 3), n ≥ N₀ →
        G.ContainsCycleThroughEdge u v n hn :=
  sorry

end
