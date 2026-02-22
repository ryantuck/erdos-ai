import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #611

For a graph G let τ(G) denote the minimal number of vertices that include at
least one from each maximal clique of G (the clique transversal number).

Is it true that if all maximal cliques in G have at least cn vertices then
τ(G) = o_c(n)?

Similarly, estimate for c > 0 the minimal k_c(n) such that if every maximal
clique in G has at least k_c(n) vertices then τ(G) < (1−c)n.

A problem of Erdős, Gallai, and Tuza [EGT92][Er94][Er99].

Known results:
- k_c(n) ≥ n^{c'/log log n} for some c' > 0 [EGT92]
- If every clique has size at least k then τ(G) ≤ n − √(kn) [EGT92]
- If every maximal clique has at least n + 3 − 2√n vertices then τ(G) = 1
  (Bollobás and Erdős, best possible)

Tags: graph theory
-/

/-- S is a maximal clique of G (as a Finset): it is a clique and no vertex
    outside S can be added while preserving the clique property. -/
def IsMaximalCliqueFS611 {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- T is a clique transversal of G if T meets every maximal clique of G
    that has at least 2 vertices. -/
def IsCliqueTransversal611 {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS611 G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number τ(G): the minimum cardinality of a clique
    transversal of G. -/
noncomputable def cliqueTransversalNum611 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal611 G T ∧ T.card = k }

/-- Every maximal clique of G with at least 2 vertices has at least m vertices. -/
def allMaxCliquesAtLeast611 {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS611 G S → 2 ≤ S.card → m ≤ S.card

/--
**Erdős Problem #611** (Main conjecture) [EGT92][Er94][Er99]:

If all maximal cliques in G have at least cn vertices then τ(G) = o_c(n).

Formulated as: for every c > 0 and ε > 0, there exists N₀ such that for all
n ≥ N₀, every graph G on n vertices in which every maximal clique has at
least ⌈c·n⌉ vertices satisfies τ(G) ≤ ε·n.
-/
theorem erdos_problem_611_main (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ G : SimpleGraph (Fin n),
        allMaxCliquesAtLeast611 G (⌈c * (n : ℝ)⌉₊) →
        (cliqueTransversalNum611 G : ℝ) ≤ ε * (n : ℝ) :=
  sorry

/--
**Erdős Problem #611** (Known bound, Erdős-Gallai-Tuza) [EGT92]:

If every maximal clique of G on n vertices has at least k vertices then
τ(G) ≤ n − √(kn).
-/
theorem erdos_problem_611_known_bound (n : ℕ) (hn : n ≥ 1)
    (G : SimpleGraph (Fin n)) (k : ℕ) (hk : k ≥ 1)
    (hclique : allMaxCliquesAtLeast611 G k) :
    (cliqueTransversalNum611 G : ℝ) ≤ (n : ℝ) - Real.sqrt ((k : ℝ) * (n : ℝ)) :=
  sorry

/--
**Erdős Problem #611** (Bollobás-Erdős):

If every maximal clique of G on n vertices has at least n + 3 − 2√n vertices
then τ(G) ≤ 1. (This threshold is best possible.)
-/
theorem erdos_problem_611_bollobas_erdos (n : ℕ) (hn : n ≥ 4)
    (G : SimpleGraph (Fin n)) :
    allMaxCliquesAtLeast611 G (n + 3 - 2 * Nat.sqrt n) →
    cliqueTransversalNum611 G ≤ 1 :=
  sorry

end
