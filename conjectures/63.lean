import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

/--
Erdős Problem #63 (Conjectured by Mihók and Erdős [Er93,Er94b,Er95,Er95d,Er96,Er97b]):
Does every graph with infinite chromatic number contain a cycle of length 2^n for
infinitely many n? (PROVED, via Liu-Montgomery [LiMo20].)

Formalized as: for every graph G with infinite chromatic number, for every bound N,
there exists n ≥ N such that G contains a cycle of length 2^n.
-/
theorem erdos_problem_63 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ n :=
  sorry
