import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card

open SimpleGraph Cardinal

/--
A graph G (on vertex type V) has chromatic number ℵ₁ if:
(1) G cannot be properly colored by any countable set of colors
    (i.e., the chromatic number exceeds ℵ₀), and
(2) G can be properly colored by a set of cardinality ℵ₁.
-/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/--
Erdős-Hajnal-Szemerédi Conjecture (Problem #110):
Is there some function F : ℕ → ℕ such that every graph G with chromatic number ℵ₁
has, for all sufficiently large n, a subgraph with chromatic number n on at most
F(n) vertices?

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82].
The analogous statement fails for graphs of chromatic number ℵ₀.
Shelah [KoSh05] proved it is consistent with ZFC that the answer is no.
Lambie-Hanson [La20] constructed a ZFC counterexample, so the conjecture is FALSE.
-/
theorem erdos_problem_110 :
    ∃ F : ℕ → ℕ,
      ∀ (V : Type*) (G : SimpleGraph V),
        HasChromaticNumberAleph1 G →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∃ H : G.Subgraph,
            H.verts.Finite ∧
            H.verts.ncard ≤ F n ∧
            H.coe.chromaticNumber = ↑n :=
  sorry
