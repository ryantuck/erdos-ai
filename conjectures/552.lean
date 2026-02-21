import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Sqrt

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #552

Determine the Ramsey number R(C₄, Sₙ), where Sₙ = K_{1,n} is the star on
n + 1 vertices.

In particular, is it true that, for any c > 0, there are infinitely many n
such that R(C₄, Sₙ) ≤ n + √n - c?

A problem of Burr, Erdős, Faudree, Rousseau, and Schelp [BEFRS89]. The known
bounds are:
  n + √n - 6n^{11/40} ≤ R(C₄, Sₙ) ≤ n + ⌈√n⌉ + 1.
The lower bound is due to [BEFRS89] and the upper bound is due to Parsons [Pa75].
Erdős offered $100 for a proof or disproof.
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The off-diagonal Ramsey number R(G₁, G₂): the minimum N such that every
    graph H on N vertices contains a copy of G₁ or its complement contains a
    copy of G₂. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G₁ H ∨ ContainsSubgraphCopy G₂ Hᶜ}

/-- The cycle graph on k vertices (k ≥ 3): vertex i is adjacent to vertex j iff
    they differ by exactly 1 modulo k. -/
def cycleGraph (k : ℕ) (hk : k ≥ 3) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val
  symm _ _ h := h.elim Or.inr Or.inl
  loopless := ⟨fun v h => by
    rcases h with h | h <;> {
      have := v.isLt
      by_cases heq : v.val + 1 = k
      · rw [heq, Nat.mod_self] at h; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at h; omega
    }⟩

/-- The star graph Sₙ = K_{1,n} on n + 1 vertices: vertex 0 is the center,
    adjacent to all other vertices. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm _ _ h := h.elim Or.inr Or.inl
  loopless := ⟨fun v h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact h2 h1⟩

/--
Erdős Problem #552 [BEFRS89]:

Is it true that, for any c > 0, there are infinitely many n such that
  R(C₄, Sₙ) ≤ n + √n - c?

Here C₄ is the cycle on 4 vertices and Sₙ = K_{1,n} is the star on n + 1
vertices. "Infinitely many" is formalised as: for every N there exists n ≥ N
satisfying the bound.
-/
theorem erdos_problem_552 :
    ∀ c : ℝ, c > 0 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (offDiagRamseyNumber (cycleGraph 4 (by omega)) (starGraph n) : ℝ) ≤
        ↑n + Real.sqrt ↑n - c :=
  sorry

end
