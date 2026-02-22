import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #842

Let $G$ be a graph on $3n$ vertices formed by taking $n$ vertex disjoint triangles
and adding a Hamiltonian cycle (with all new edges) between these vertices.
Does $G$ have chromatic number at most $3$?

The answer is yes, proved by Fleischner and Stiebitz [FlSt92].
-/

/-- The graph of n vertex-disjoint triangles on 3n vertices. Vertices 3i, 3i+1, 3i+2
    form the i-th triangle. -/
def triangleGraph842 (n : ℕ) : SimpleGraph (Fin (3 * n)) where
  Adj u v := u ≠ v ∧ u.val / 3 = v.val / 3
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- A permutation σ on Fin m is a single m-cycle (Hamiltonian cycle): applying σ
    repeatedly from any vertex can reach every other vertex. -/
def IsSingleCycle842 {m : ℕ} (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ u v : Fin m, ∃ k : ℕ, (σ ^ k) u = v

/-- The cycle graph induced by a permutation σ: vertices u and v are adjacent
    iff σ(u) = v or σ(v) = u. -/
def cycleGraphOfPerm842 {m : ℕ} (σ : Equiv.Perm (Fin m)) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ (σ u = v ∨ σ v = u)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/--
Erdős Problem #842 [Er92b]:

Let G be a graph on 3n vertices formed by taking n vertex-disjoint triangles
and adding a Hamiltonian cycle (with all new edges). Then G has chromatic
number at most 3.

Proved by Fleischner and Stiebitz [FlSt92].
-/
theorem erdos_problem_842 (n : ℕ) (hn : n ≥ 1)
    (σ : Equiv.Perm (Fin (3 * n)))
    (hcycle : IsSingleCycle842 σ)
    (hnew : ∀ u v : Fin (3 * n),
      (cycleGraphOfPerm842 σ).Adj u v → ¬(triangleGraph842 n).Adj u v) :
    (triangleGraph842 n ⊔ cycleGraphOfPerm842 σ).chromaticNumber ≤ 3 :=
  sorry

end
