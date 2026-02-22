import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Filter

noncomputable section

/-!
# Erdős Problem #610

For a graph G let τ(G) denote the minimal number of vertices that include at
least one from each maximal clique of G (the clique transversal number).

Estimate τ(G). In particular, is it true that if G has n vertices then
  τ(G) ≤ n − ω(n)√n
for some ω(n) → ∞, or even
  τ(G) ≤ n − c√(n log n)
for some absolute constant c > 0?

A problem of Erdős, Gallai, and Tuza [EGT92], who proved that
  τ(G) ≤ n − √(2n) + O(1).

Tags: graph theory
-/

/-- S is a maximal clique of G (as a Finset): it is a clique and no vertex
    outside S can be added while preserving the clique property. -/
def IsMaximalCliqueFS610 {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- T is a clique transversal of G if T meets every maximal clique of G
    that has at least 2 vertices. -/
def IsCliqueTransversal610 {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS610 G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number τ(G): the minimum cardinality of a clique
    transversal of G. -/
noncomputable def cliqueTransversalNum610 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal610 G T ∧ T.card = k }

/--
**Erdős Problem #610** (Weak form) [EGT92]:

There exists a function ω : ℕ → ℝ with ω(n) → ∞ such that for every graph G
on n vertices, τ(G) ≤ n − ω(n)·√n.
-/
theorem erdos_problem_610_weak :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ n : ℕ, n ≥ 1 →
        ∀ G : SimpleGraph (Fin n),
          (cliqueTransversalNum610 G : ℝ) ≤ (n : ℝ) - ω n * Real.sqrt (n : ℝ) :=
  sorry

/--
**Erdős Problem #610** (Strong form) [EGT92][Er94][Er99]:

There exists c > 0 such that for every graph G on n vertices,
τ(G) ≤ n − c·√(n·log n).
-/
theorem erdos_problem_610_strong :
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∀ G : SimpleGraph (Fin n),
          (cliqueTransversalNum610 G : ℝ) ≤
            (n : ℝ) - c * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
  sorry

/--
**Erdős Problem #610** (Known bound, Erdős-Gallai-Tuza) [EGT92]:

There exists C > 0 such that for every graph G on n vertices,
τ(G) ≤ n − √(2n) + C.
-/
theorem erdos_problem_610_known_bound :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
      ∀ G : SimpleGraph (Fin n),
        (cliqueTransversalNum610 G : ℝ) ≤ (n : ℝ) - Real.sqrt (2 * (n : ℝ)) + C :=
  sorry

end
