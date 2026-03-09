import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise

namespace Erdos567

open SimpleGraph Finset

/--
Q₃: the 3-dimensional hypercube graph on Fin 8.
Two vertices are adjacent iff their binary representations differ in exactly one bit.
-/
def Q3 : SimpleGraph (Fin 8) where
  Adj i j :=
    (i : ℕ) ^^^ (j : ℕ) = 1 ∨ (i : ℕ) ^^^ (j : ℕ) = 2 ∨ (i : ℕ) ^^^ (j : ℕ) = 4
  symm := by
    intro a b h
    simp only [Nat.xor_comm (a : ℕ) (b : ℕ)] at h
    exact h
  loopless := ⟨by
    intro a h
    simp only [Nat.xor_self] at h
    omega⟩

/--
K_{3,3}: the complete bipartite graph with parts {0,1,2} and {3,4,5}.
-/
def K33 : SimpleGraph (Fin 6) where
  Adj i j := (i.val < 3 ∧ 3 ≤ j.val) ∨ (j.val < 3 ∧ 3 ≤ i.val)
  symm := by
    intro a b h
    exact h.elim (fun h => Or.inr h) (fun h => Or.inl h)
  loopless := ⟨by
    intro a h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/--
H₅: the graph K₄* obtained by subdividing one edge of K₄.
Equivalently, C₅ with two vertex-disjoint chords.
Constructed as K₄ on {0,1,2,3} with edge {2,3} replaced by path 2-4-3.
Edges: {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,4}, {3,4}.
-/
def H5 : SimpleGraph (Fin 5) where
  Adj i j :=
    i ≠ j ∧
    ((i.val < 4 ∧ j.val < 4 ∧ ¬(min i.val j.val = 2 ∧ max i.val j.val = 3)) ∨
     (min i.val j.val = 2 ∧ max i.val j.val = 4) ∨
     (min i.val j.val = 3 ∧ max i.val j.val = 4))
  symm := by
    intro a b ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rw [min_comm, max_comm]
    exact h.imp (fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩) id
  loopless := ⟨fun a h => h.1 rfl⟩

/-- A graph has no isolated vertices: every vertex has at least one neighbor. -/
def HasNoIsolatedVertices {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ v : V, 0 < H.degree v

/--
A graph F has the size Ramsey property for (G, H) if every 2-coloring of
the edges of F yields either a monochromatic copy of G in color 1 or a
monochromatic copy of H in color 2.
-/
def HasSizeRamseyProp {V₁ V₂ W : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂)
    (F : SimpleGraph W) [DecidableRel F.Adj] : Prop :=
  ∀ c : Sym2 W → Bool,
    (∃ f : V₁ ↪ W, ∀ u v, G.Adj u v →
      F.Adj (f u) (f v) ∧ c s(f u, f v) = true) ∨
    (∃ f : V₂ ↪ W, ∀ u v, H.Adj u v →
      F.Adj (f u) (f v) ∧ c s(f u, f v) = false)

/--
Erdős Problem #567 [EFRS93, Er95]:

Let G be either Q₃, K_{3,3}, or H₅ (the graph obtained from K₄ by subdividing
one edge, equivalently C₅ with two vertex-disjoint chords). Is it true that,
if H has m edges and no isolated vertices, then R̂(G,H) ≪ m?

In other words, is G Ramsey size linear? A special case of Problem #566.
In [Er95] Erdős specifically asks about the case G = K_{3,3}.
-/
theorem erdos_problem_567_Q3 :
    ∃ c : ℕ, 0 < c ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        HasNoIsolatedVertices H →
        ∃ (q : ℕ) (F : SimpleGraph (Fin q)) (_ : DecidableRel F.Adj),
          F.edgeFinset.card ≤ c * H.edgeFinset.card ∧
          HasSizeRamseyProp Q3 H F :=
  sorry

theorem erdos_problem_567_K33 :
    ∃ c : ℕ, 0 < c ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        HasNoIsolatedVertices H →
        ∃ (q : ℕ) (F : SimpleGraph (Fin q)) (_ : DecidableRel F.Adj),
          F.edgeFinset.card ≤ c * H.edgeFinset.card ∧
          HasSizeRamseyProp K33 H F :=
  sorry

theorem erdos_problem_567_H5 :
    ∃ c : ℕ, 0 < c ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        HasNoIsolatedVertices H →
        ∃ (q : ℕ) (F : SimpleGraph (Fin q)) (_ : DecidableRel F.Adj),
          F.edgeFinset.card ≤ c * H.edgeFinset.card ∧
          HasSizeRamseyProp H5 H F :=
  sorry

end Erdos567
