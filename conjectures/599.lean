import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #599

Let G be a (possibly infinite) graph and A, B be disjoint independent sets of
vertices. Must there exist a family P of disjoint paths between A and B and a
set S which contains exactly one vertex from each path in P, and such that every
path between A and B contains at least one vertex from S?

Sometimes known as the Erdős-Menger conjecture. When G is finite this is
equivalent to Menger's theorem. Erdős was interested in the case when G is
infinite. This was proved by Aharoni and Berger [AhBe09].
-/

/--
Erdős Problem #599 (Erdős-Menger Conjecture) [Er81][Er87]:

For any graph G and disjoint independent sets A, B, there exists a family of
pairwise vertex-disjoint A-B paths and a set S containing exactly one vertex
from each path, such that S separates A from B (every A-B walk meets S).
-/
theorem erdos_problem_599 {V : Type*} (G : SimpleGraph V)
    (A B : Set V) (hAB : Disjoint A B)
    (hA : ∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v)
    (hB : ∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v) :
    ∃ (ι : Type) (src : ι → V) (dst : ι → V)
      (p : (i : ι) → G.Walk (src i) (dst i))
      (S : Set V),
      (∀ i, src i ∈ A) ∧
      (∀ i, dst i ∈ B) ∧
      (∀ i, (p i).IsPath) ∧
      (∀ i j, i ≠ j → List.Disjoint (p i).support (p j).support) ∧
      (∀ i, ∃! v, v ∈ S ∧ v ∈ (p i).support) ∧
      (∀ (x : V) (y : V), x ∈ A → y ∈ B →
        ∀ (w : G.Walk x y), ∃ s ∈ S, s ∈ w.support) :=
  sorry

end
