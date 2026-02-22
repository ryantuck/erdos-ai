import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Classical

noncomputable section

/-!
# Erdős Problem #615

Does there exist some constant c > 0 such that if G is a graph with n vertices
and ≥ (1/8 - c)n² edges then G must contain either a K₄ or an independent set
on at least n / log n vertices?

Equivalently, if rt(n; k, ℓ) denotes the Ramsey-Turán number (maximum number of
edges in a K_k-free graph on n vertices with independence number < ℓ), the
question asks whether rt(n; 4, ⌈n / log n⌉) < (1/8 - c)n² for some c > 0.

A problem of Erdős, Hajnal, Simonovits, Sós, and Szemerédi [EHSSS93].

Erdős, Hajnal, Sós, and Szemerédi [EHSS83] proved that for any fixed ε > 0,
  rt(n; 4, εn) < (1/8 + o(1))n².

Sudakov [Su03] proved that rt(n; 4, n·e^{-f(n)}) = o(n²) whenever
  f(n)/√(log n) → ∞.

Disproved by Fox, Loh, and Zhao [FLZ15], who showed that
  rt(n; 4, n·e^{-f(n)}) ≥ (1/8 - o(1))n²
whenever f(n) = o(√(log n / log log n)).

Tags: graph theory, ramsey theory
-/

/-- A set of vertices is independent in G if no two distinct vertices in the set
    are adjacent. -/
def IsIndependentSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- The Ramsey-Turán number rt(n; k, ℓ): the maximum number of edges in a graph
    on n vertices that contains no k-clique and has no independent set of size ≥ ℓ.
    Returns 0 if no such graph exists. -/
noncomputable def ramseyTuranNumber (n k ℓ : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.edgeFinset.card = m ∧ G.CliqueFree k ∧
    ∀ S : Finset (Fin n), IsIndependentSet G S → S.card < ℓ}

/--
**Erdős Problem #615** (DISPROVED) [EHSSS93]:

There does NOT exist c > 0 such that for all sufficiently large n, every graph G
on n vertices with at least (1/8 - c)n² edges contains either a K₄ or an
independent set of size at least n / log n.

Disproved by Fox, Loh, and Zhao [FLZ15].
-/
theorem erdos_problem_615 :
    ¬ ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        (G.edgeFinset.card : ℝ) ≥ (1 / 8 - c) * (n : ℝ) ^ 2 →
        (¬G.CliqueFree 4) ∨
        ∃ S : Finset (Fin n), (S.card : ℝ) ≥ (n : ℝ) / Real.log (n : ℝ) ∧
          IsIndependentSet G S :=
  sorry

/--
**Erdős-Hajnal-Sós-Szemerédi** [EHSS83]:

For any fixed ε > 0, every K₄-free graph on n vertices with independence
number < εn has fewer than (1/8 + o(1))n² edges.
-/
theorem erdos_problem_615_EHSS (ε : ℝ) (hε : ε > 0) :
    ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 4 →
        (∀ S : Finset (Fin n), IsIndependentSet G S → (S.card : ℝ) < ε * (n : ℝ)) →
        (G.edgeFinset.card : ℝ) ≤ (1 / 8 + δ) * (n : ℝ) ^ 2 :=
  sorry

end
