import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #551

Prove that R(C_k, K_n) = (k-1)(n-1) + 1 for k ≥ n ≥ 3 (except when n = k = 3).

Here R(C_k, K_n) is the off-diagonal Ramsey number, C_k is the cycle graph on
k vertices, and K_n is the complete graph on n vertices.

Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS78]. This identity was
proved for k > n²-2 by Bondy and Erdős [BoEr73], extended to k ≥ 4n+2 by
Nikiforov [Ni05], and established for sufficiently large n by Keevash, Long,
and Skokan [KLS21].
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

/--
Erdős Problem #551 [EFRS78]:

Prove that R(C_k, K_n) = (k-1)(n-1) + 1 for k ≥ n ≥ 3, except when n = k = 3.

Here C_k is the cycle graph on k vertices and K_n is the complete graph on n
vertices (expressed as ⊤ : SimpleGraph (Fin n)).
-/
theorem erdos_problem_551 (k n : ℕ) (hk : k ≥ n) (hn : n ≥ 3) (hne : ¬(k = 3 ∧ n = 3)) :
    offDiagRamseyNumber (cycleGraph k (by omega)) (⊤ : SimpleGraph (Fin n)) =
      (k - 1) * (n - 1) + 1 :=
  sorry

end
