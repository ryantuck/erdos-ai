import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #720 (PROVED)

Let R̂(G) denote the size Ramsey number, the minimal number of edges m such
that there is a graph H with m edges such that in any 2-colouring of the
edges of H there is a monochromatic copy of G.

The original questions asked:
1. Is it true that R̂(Pₙ)/n → ∞?
2. Is it true that R̂(Pₙ)/n² → 0?
3. Is it true that R̂(Cₙ) = o(n²)?

Answered by Beck [Be83b], who proved the much stronger result that
R̂(Pₙ) ≪ n and R̂(Cₙ) ≪ n (i.e., the size Ramsey numbers are linear).

This resolves all three questions:
- Question 1 is answered in the NEGATIVE (R̂(Pₙ)/n is bounded).
- Questions 2 and 3 are answered in the AFFIRMATIVE (in a much stronger form).
-/

/-- The path graph P_n of length n: n+1 vertices {0, ..., n} where vertex i
    is adjacent to vertex i+1. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := ⟨fun x h => by rcases h with h | h <;> omega⟩

/-- The cycle graph C_n on n vertices (n ≥ 3). Vertex i is adjacent to
    vertex (i+1) mod n and vertex (i-1) mod n. -/
def cycleGraph (n : ℕ) (_ : n ≥ 3) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % n ∨ i.val = (j.val + 1) % n)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The size Ramsey number R̂(G): the minimum number of edges in a graph H
    that is Ramsey for G.

    A graph H on N vertices is Ramsey for G if every 2-coloring of the edges
    of H (represented as a symmetric function c : Fin N → Fin N → Bool)
    contains a monochromatic copy of G, i.e., an injective map f from the
    vertices of G into Fin N that preserves adjacency in H and maps all
    edges to the same color. -/
noncomputable def sizeRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (N : ℕ) (H : SimpleGraph (Fin N)),
    Nat.card H.edgeSet = m ∧
    ∀ (c : Fin N → Fin N → Bool),
      (∀ i j, c i j = c j i) →
      ∃ (b : Bool) (f : V → Fin N),
        Function.Injective f ∧
        (∀ u v, G.Adj u v → H.Adj (f u) (f v)) ∧
        (∀ u v, G.Adj u v → c (f u) (f v) = b)}

/--
Erdős Problem #720, Part 1 (Beck's theorem for paths):

The size Ramsey number of the path Pₙ is at most linear in n.
That is, there exists a constant C such that R̂(Pₙ) ≤ C · (n + 1) for all n.

This disproves the conjecture that R̂(Pₙ)/n → ∞ and proves R̂(Pₙ)/n² → 0.
-/
theorem erdos_problem_720_paths :
    ∃ C : ℕ, ∀ n : ℕ,
      sizeRamseyNumber (pathGraph n) ≤ C * (n + 1) :=
  sorry

/--
Erdős Problem #720, Part 2 (Beck's theorem for cycles):

The size Ramsey number of the cycle Cₙ is at most linear in n.
That is, there exists a constant C such that R̂(Cₙ) ≤ C · n for all n ≥ 3.

This proves (in a much stronger form) the conjecture that R̂(Cₙ) = o(n²).
-/
theorem erdos_problem_720_cycles :
    ∃ C : ℕ, ∀ n : ℕ, (hn : n ≥ 3) →
      sizeRamseyNumber (cycleGraph n hn) ≤ C * n :=
  sorry

end
