import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #60

Does every graph on n vertices with > ex(n; C₄) edges contain ≫ n^{1/2} many
copies of C₄?

Conjectured by Erdős and Simonovits [Er90][Er93], who could not even prove that
at least 2 copies of C₄ are guaranteed.

The behaviour of ex(n; C₄) is the subject of problem [765].
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). -/
def cycleGraph60 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- G contains H as a subgraph (via an injective homomorphism). -/
def ContainsSubgraph60 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- ex(n; H): maximum number of edges in an H-free simple graph on n vertices. -/
noncomputable def extremalNumber60 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph60 G H ∧ G.edgeSet.ncard = m}

/-- The number of labeled copies of C₄ in G: injective maps f : Fin 4 → Fin n
    preserving C₄ adjacency. Each unordered C₄ subgraph yields 8 labeled copies
    (4 rotations × 2 reflections). -/
noncomputable def labeledC4Count (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun (f : Fin 4 → Fin n) =>
    Function.Injective f ∧
    ∀ i : Fin 4, G.Adj (f i) (f (i + 1)))).card

/--
Erdős Problem #60 [Er90][Er93]:

Does every graph on n vertices with more than ex(n; C₄) edges contain
≫ n^{1/2} copies of C₄?

Formally: there exist c > 0 and N₀ such that for all n ≥ N₀, every graph G on
n vertices with more than ex(n; C₄) edges has at least c · n^{1/2} labeled
copies of C₄.
-/
theorem erdos_problem_60 :
    ∃ (c : ℝ) (_ : c > 0) (N₀ : ℕ),
    ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber60 (cycleGraph60 4 (by omega)) n →
      (labeledC4Count n G : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
