import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #557

Let R_k(G) denote the minimal m such that if the edges of K_m are k-coloured
then there is a monochromatic copy of G. Is it true that
  R_k(T) ≤ kn + O(1)
for any tree T on n vertices?

A problem of Erdős and Graham. This would be best possible since, for example,
R_k(S_n) ≥ kn - O(k) if S_n = K_{1,n-1} is a star on n vertices.
-/

/-- The k-colour Ramsey number R_k(G): the minimum N such that for every
    k-colouring of the edges of K_N, there is a monochromatic copy of G.

    A k-colouring is a symmetric function c : Fin N → Fin N → Fin k.
    A monochromatic copy of G in colour a is an injective map f : V → Fin N
    such that every edge of G maps to an edge of colour a. -/
noncomputable def multicolorRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a : Fin k) (f : V → Fin N), Function.Injective f ∧
      ∀ u v, G.Adj u v → c (f u) (f v) = a}

/--
Erdős Problem #557 [ErGr75]:

There exists an absolute constant C such that for all k ≥ 1, all n ≥ 1, and
all trees T on n vertices, R_k(T) ≤ kn + C.
-/
theorem erdos_problem_557 :
    ∃ C : ℕ, ∀ (n : ℕ) (hn : n ≥ 1) (T : SimpleGraph (Fin n)),
      T.IsTree →
      ∀ k : ℕ, k ≥ 1 →
        multicolorRamseyNumber T k ≤ k * n + C :=
  sorry

end
