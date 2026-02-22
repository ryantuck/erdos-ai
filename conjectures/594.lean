import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Basic

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #594

Does every graph $G$ with chromatic number $\geq \aleph_1$ contain all
sufficiently large odd cycles?

A problem of Erdős and Hajnal (who proved this for chromatic number ≥ ℵ₂).
This was proved by Erdős, Hajnal, and Shelah [EHS74].

https://www.erdosproblems.com/594
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

/-- G contains a copy of H: there is an injective map preserving adjacency. -/
def SimpleGraph.ContainsCopy {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #594 [ErHa66] [Er69b]:

Every graph with uncountable chromatic number (i.e., chromatic number ≥ ℵ₁)
contains all sufficiently large odd cycles. That is, there exists N₀ such
that for all odd n ≥ N₀ (with n ≥ 3), the graph contains C_n as a subgraph.

A problem of Erdős and Hajnal (who proved this for chromatic number ≥ ℵ₂).
Proved by Erdős, Hajnal, and Shelah [EHS74].
-/
theorem erdos_problem_594 {V : Type*} (G : SimpleGraph V)
    (hG : HasUncountableChromaticNumber G) :
    ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : n ≥ 3), Odd n → n ≥ N₀ →
      G.ContainsCopy (cycleGraph n hn) :=
  sorry

end
