import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

/--
Erdős Problem #61 (Erdős-Hajnal Conjecture) [ErHa89, Er90, Er93, Er97f, Va99]:

For any graph H, is there some c = c(H) > 0 such that every graph G on n
vertices that does not contain H as an induced subgraph contains either a
complete graph or independent set on ≥ n^c vertices?

Conjectured by Erdős and Hajnal, who proved the weaker bound
exp(c_H √(log n)). Improved by Bucić, Nguyen, Scott, and Seymour to
exp(c_H √(log n · log log n)).
-/
theorem erdos_problem_61 :
    ∀ (H : SimpleGraph (Fin k)),
      ∃ c : ℝ, 0 < c ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          (¬ ∃ (f : Fin k ↪ Fin n), ∀ i j, H.Adj i j ↔ G.Adj (f i) (f j)) →
          ∃ (S : Finset (Fin n)),
            (S.card : ℝ) ≥ (n : ℝ) ^ c ∧
            (G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n))) :=
  sorry
