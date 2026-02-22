import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Sum

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #560

Let R̂(G) denote the size Ramsey number, the minimal number of edges m such
that there is a graph H with m edges such that in any 2-colouring of the
edges of H there is a monochromatic copy of G.

Determine R̂(K_{n,n}), where K_{n,n} is the complete bipartite graph with n
vertices in each component.

Known bounds:
  (1/60) n² 2ⁿ < R̂(K_{n,n}) < (3/2) n³ 2ⁿ

The lower bound (for n ≥ 6) was proved by Erdős and Rousseau [ErRo93].
The upper bound was proved by Erdős, Faudree, Rousseau, and Schelp [EFRS78b]
and Nešetřil and Rödl [NeRo78].

Conlon, Fox, and Wigderson [CFW23] conjecture that R̂(K_{n,n}) ≍ n³ 2ⁿ.
-/

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
Erdős Problem #560, lower bound [ErRo93]:

For all n ≥ 6, R̂(K_{n,n}) > (1/60) n² 2ⁿ.
-/
theorem erdos_problem_560_lower :
    ∀ n : ℕ, n ≥ 6 →
      (sizeRamseyNumber (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) >
        (1 / 60 : ℝ) * (n : ℝ) ^ 2 * 2 ^ n :=
  sorry

/--
Erdős Problem #560, upper bound [EFRS78b, NeRo78]:

For all n ≥ 1, R̂(K_{n,n}) < (3/2) n³ 2ⁿ.
-/
theorem erdos_problem_560_upper :
    ∀ n : ℕ, n ≥ 1 →
      (sizeRamseyNumber (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) <
        (3 / 2 : ℝ) * (n : ℝ) ^ 3 * 2 ^ n :=
  sorry

/--
Erdős Problem #560, conjecture [CFW23]:

R̂(K_{n,n}) ≍ n³ 2ⁿ, i.e., there exist constants C₁, C₂ > 0 and N₀ such
that for all n ≥ N₀,
  C₁ · n³ · 2ⁿ ≤ R̂(K_{n,n}) ≤ C₂ · n³ · 2ⁿ.
-/
theorem erdos_problem_560 :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * (n : ℝ) ^ 3 * 2 ^ n ≤
        (sizeRamseyNumber (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) ∧
      (sizeRamseyNumber (completeBipartiteGraph (Fin n) (Fin n)) : ℝ) ≤
        C₂ * (n : ℝ) ^ 3 * 2 ^ n :=
  sorry

end
