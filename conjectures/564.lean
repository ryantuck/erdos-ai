import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

open Finset

/--
Iterated exponential tower: `tower 0 x = x` and `tower (k+1) x = 2^(tower k x)`.
So `tower k x` is a tower of 2s of height k with x at the top.
-/
def tower : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => 2 ^ tower k x

/--
`HypergraphRamseyProp r n m` asserts that every 2-coloring of the r-element
subsets of an m-element set yields a monochromatic complete r-uniform hypergraph
on n vertices. That is, for every coloring c of subsets of `Fin m`, there exists
a set S of size ≥ n such that all r-element subsets of S receive the same color.
-/
def HypergraphRamseyProp (r n m : ℕ) : Prop :=
  ∀ c : Finset (Fin m) → Bool,
    ∃ (S : Finset (Fin m)) (color : Bool),
      n ≤ S.card ∧
      ∀ T : Finset (Fin m), T ⊆ S → T.card = r → c T = color

/--
Erdős Problem #564 [EHR65, Er81, Er97c]:

Let R₃(n) be the minimal m such that if we 2-colour all edges of the complete
3-uniform hypergraph on m vertices then there must be a monochromatic copy of
the complete 3-uniform hypergraph on n vertices.

Is there some constant c > 0 such that R₃(n) ≥ 2^{2^{cn}}?

A special case of problem #562. A problem of Erdős, Hajnal, and Rado, who
proved the bounds 2^{cn²} < R₃(n) < 2^{2^n} for some constant c > 0.
The conjecture asks whether the lower bound can be improved to doubly
exponential in n.

We state this as: there exist c ≥ 1 and n₀ such that for all n ≥ n₀,
R₃(n) ≥ tower(2, n/c), i.e., no 2-coloring of the 3-element subsets
of a set of size tower(2, n/c) - 1 is forced to contain a monochromatic
complete 3-uniform hypergraph on n vertices.
-/
theorem erdos_problem_564 :
    ∃ (c n₀ : ℕ), 0 < c ∧
      ∀ n : ℕ, n ≥ n₀ →
        ¬ HypergraphRamseyProp 3 n (tower 2 (n / c) - 1) :=
  sorry
