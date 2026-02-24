import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #87

Let ε > 0. Is it true that, if k is sufficiently large, then
  R(G) > (1 - ε)^k · R(k)
for every graph G with chromatic number χ(G) = k?

Even stronger, is there some c > 0 such that, for all large k,
  R(G) > c · R(k)
for every graph G with chromatic number χ(G) = k?

Here R(G) is the (diagonal) graph Ramsey number: the minimum N such that every
2-colouring of K_N contains a monochromatic copy of G, and R(k) := R(K_k).

Erdős originally conjectured R(G) ≥ R(k) for all G with χ(G) = k, which fails
already for k = 4: Faudree and McKay showed R(W) = 17 < 18 = R(4) for the
pentagonal wheel W.

Reference: [Er95, p.14]
https://www.erdosproblems.com/87
-/

/-- An injective graph homomorphism (embedding) from H into G:
    G contains a copy of H as a subgraph. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The (diagonal) graph Ramsey number R(H): the minimum N such that every simple
    graph G on N vertices either contains a copy of H as a subgraph or whose
    complement contains a copy of H (equivalently, every 2-colouring of K_N
    contains a monochromatic copy of H). -/
noncomputable def graphRamseyNumber {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsSubgraph G H ∨ containsSubgraph Gᶜ H}

/-- The classical diagonal Ramsey number R(k) := R(K_k, K_k). -/
noncomputable def diagRamsey (k : ℕ) : ℕ :=
  graphRamseyNumber (⊤ : SimpleGraph (Fin k))

/--
**Erdős Problem #87** — Weak form (open):

For every ε ∈ (0, 1), if k is sufficiently large, then R(G) > (1 - ε)^k · R(k)
for every finite graph G with chromatic number χ(G) = k.
-/
theorem erdos_problem_87_weak :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      (diagRamsey k : ℝ) * (1 - ε) ^ k < (graphRamseyNumber G : ℝ) :=
  sorry

/--
**Erdős Problem #87** — Strong form (open):

There exists c > 0 such that for all sufficiently large k and every finite graph G
with chromatic number χ(G) = k, we have R(G) > c · R(k).
-/
theorem erdos_problem_87_strong :
    ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      c * (diagRamsey k : ℝ) < (graphRamseyNumber G : ℝ) :=
  sorry

end
