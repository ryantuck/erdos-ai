import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #561

Let R̂(F₁, F₂) denote the two-color size Ramsey number: the minimal number of
edges m such that there is a graph H with m edges such that in any 2-colouring
of the edges of H there is a copy of F₁ in color 1 or a copy of F₂ in color 2.

Let F₁ = ⋃_{i ≤ s} K_{1,nᵢ} and F₂ = ⋃_{j ≤ t} K_{1,mⱼ} with
n₁ ≥ ⋯ ≥ nₛ ≥ 1 and m₁ ≥ ⋯ ≥ mₜ ≥ 1.

Prove that R̂(F₁, F₂) = ∑_{2 ≤ k ≤ s+t} lₖ
where lₖ = max{nᵢ + mⱼ - 1 : i + j = k}.
-/

/-- Disjoint union of star graphs K_{1,deg(0)} ∪ ⋯ ∪ K_{1,deg(s-1)}.
    Vertex ⟨i, j⟩ belongs to the i-th star; j = 0 is the center. -/
def disjointUnionStars (s : ℕ) (deg : Fin s → ℕ) :
    SimpleGraph (Σ i : Fin s, Fin (deg i + 1)) where
  Adj x y := x.1 = y.1 ∧ ((x.2.val = 0 ∧ y.2.val ≠ 0) ∨ (x.2.val ≠ 0 ∧ y.2.val = 0))
  symm {_x} {_y} := fun ⟨heq, h⟩ =>
    ⟨heq.symm, h.elim (fun ⟨a, b⟩ => Or.inr ⟨b, a⟩) (fun ⟨a, b⟩ => Or.inl ⟨b, a⟩)⟩
  loopless := ⟨fun _ ⟨_, h⟩ =>
    h.elim (fun ⟨a, b⟩ => b a) (fun ⟨a, b⟩ => a b)⟩

/-- The two-color size Ramsey number R̂(G₁, G₂): the minimum number of edges in
    a graph H such that for every 2-coloring of the edges of H, either color 1
    contains a copy of G₁ or color 2 contains a copy of G₂. -/
noncomputable def twoColorSizeRamseyNumber {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {m : ℕ | ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    H.edgeSet.ncard = m ∧
    ∀ c : Fin n → Fin n → Bool,
      (∀ i j, c i j = c j i) →
      (∃ f : V₁ → Fin n, Function.Injective f ∧
        ∀ u v, G₁.Adj u v → H.Adj (f u) (f v) ∧ c (f u) (f v) = true) ∨
      (∃ f : V₂ → Fin n, Function.Injective f ∧
        ∀ u v, G₂.Adj u v → H.Adj (f u) (f v) ∧ c (f u) (f v) = false)}

/-- lFun s t n m k = max{n(i) + m(j) - 1 : i + j = k} for 0-indexed i < s, j < t.
    Returns 0 when no valid (i, j) pair exists with i + j = k. -/
def lFun (s t : ℕ) (n : Fin s → ℕ) (m : Fin t → ℕ) (k : ℕ) : ℕ :=
  (Finset.filter (fun p : Fin s × Fin t => p.1.val + p.2.val = k) Finset.univ).sup
    (fun p => n p.1 + m p.2 - 1)

/--
Erdős Problem #561 [BEFRS78]:

Let R̂(F₁, F₂) denote the two-color size Ramsey number. Let F₁ and F₂ be
disjoint unions of stars:
  F₁ = K_{1,n₀} ∪ ⋯ ∪ K_{1,n_{s-1}}  with  n₀ ≥ ⋯ ≥ n_{s-1} ≥ 1
  F₂ = K_{1,m₀} ∪ ⋯ ∪ K_{1,m_{t-1}}  with  m₀ ≥ ⋯ ≥ m_{t-1} ≥ 1

Then R̂(F₁, F₂) = ∑_{k=0}^{s+t-2} lₖ where
  lₖ = max{nᵢ + mⱼ - 1 : i + j = k}.
-/
theorem erdos_problem_561
    (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1)
    (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn_pos : ∀ i, n i ≥ 1)
    (hm_pos : ∀ j, m j ≥ 1)
    (hn_mono : ∀ i₁ i₂ : Fin s, i₁ ≤ i₂ → n i₂ ≤ n i₁)
    (hm_mono : ∀ j₁ j₂ : Fin t, j₁ ≤ j₂ → m j₂ ≤ m j₁) :
    twoColorSizeRamseyNumber
      (disjointUnionStars s n)
      (disjointUnionStars t m) =
    Finset.sum (Finset.range (s + t - 1)) (lFun s t n m) :=
  sorry

end
