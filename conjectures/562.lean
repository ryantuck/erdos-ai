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
Erdős Problem #562 [EHR65]:

Let R_r(n) denote the r-uniform hypergraph Ramsey number: the minimal m such
that if we 2-colour all edges of the complete r-uniform hypergraph on m vertices
then there must be some monochromatic copy of the complete r-uniform hypergraph
on n vertices.

Prove that, for r ≥ 3, log_{r-1} R_r(n) ≍_r n, where log_{r-1} denotes the
(r-1)-fold iterated logarithm. That is, R_r(n) grows like a tower of 2s of
height r-1 applied to Θ(n).

A problem of Erdős, Hajnal, and Rado. The upper bound R_r(n) ≤ tower(r-1, O(n²))
is due to Erdős and Rado (1952). The main open challenge is the lower bound.

We state the conjecture as: for each r ≥ 3, there exist positive constants c, C
and a threshold n₀ such that for all n ≥ n₀,
  tower(r-1, n/c) ≤ R_r(n) ≤ tower(r-1, C·n).
-/
theorem erdos_problem_562 :
    ∀ r : ℕ, r ≥ 3 →
      ∃ (c C n₀ : ℕ), 0 < c ∧ 0 < C ∧
        ∀ n : ℕ, n ≥ n₀ →
          -- Upper bound: R_r(n) ≤ tower(r-1, C·n)
          HypergraphRamseyProp r n (tower (r - 1) (C * n)) ∧
          -- Lower bound: R_r(n) > tower(r-1, n/c) - 1, i.e., R_r(n) ≥ tower(r-1, n/c)
          ¬ HypergraphRamseyProp r n (tower (r - 1) (n / c) - 1) :=
  sorry
