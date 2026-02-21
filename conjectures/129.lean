import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #129

Let R(n; k, r) be the smallest N such that if the edges of K_N are r-coloured
then there is a set of n vertices which does not contain a copy of K_k in at
least one of the r colours. Erdős and Gyárfás conjectured that there exists a
constant C = C(r) > 1 such that R(n; 3, r) < C^(√n).

Note: As pointed out by Antonio Girao, the problem as stated is easily
disproved. A probabilistic argument shows R(n; 3, 2) ≥ C^n for some C > 1,
contradicting the claimed bound. The correct formulation is unclear.
-/

/-- An r-edge-coloring of the complete graph K_N: a function that assigns a
    color in Fin r to each ordered pair of distinct vertices. -/
def EdgeColoring (N r : ℕ) : Type := Fin N → Fin N → Fin r

/-- A vertex set S is monochromatic-K_k-free in color c under coloring χ if
    there is no k-element subset of S in which every pair of distinct vertices
    receives color c. -/
def IsMonoKkFree {N r : ℕ} (χ : EdgeColoring N r) (c : Fin r)
    (k : ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ χ x y ≠ c

/-- The generalized Ramsey number R(n; k, r): the smallest N such that for
    every r-coloring of the edges of K_N, there exists a set of n vertices and
    a color c such that the set is K_k-free in color c. -/
noncomputable def multicolorRamseyNum (n k r : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (χ : EdgeColoring N r),
    ∃ (S : Finset (Fin N)) (c : Fin r),
      S.card = n ∧ IsMonoKkFree χ c k S}

/--
Erdős–Gyárfás Conjecture (Problem #129) [Er97b]:
For every r ≥ 1, there exists a constant C = C(r) > 1 such that
R(n; 3, r) < C^(√n) for all positive integers n.

Erdős and Gyárfás proved the lower bound R(n; 3, r) > C^(√n) for some C > 1
via the probabilistic method. Note that when r = k = 2 we recover the classic
Ramsey numbers. Erdős conjectured more generally that for all r, k ≥ 2 there
exist C₁, C₂ > 1 (depending only on r) such that
  C₁^(n^(1/(k-1))) < R(n; k, r) < C₂^(n^(1/(k-1))).

As observed by Antonio Girao, the problem as stated is easily disproved:
a probabilistic coloring of K_N (each edge independently uniformly at random
in r colors) shows R(n; 3, 2) ≥ C^n, contradicting the conjecture.
-/
theorem erdos_problem_129 :
    ∀ r : ℕ, 1 ≤ r →
      ∃ C : ℝ, 1 < C ∧
        ∀ n : ℕ, (multicolorRamseyNum n 3 r : ℝ) < C ^ Real.sqrt (n : ℝ) :=
  sorry
