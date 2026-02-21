import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter

/-!
# Erdős Problem #378

Let r ≥ 0. Does the density of integers n for which C(n,k) is squarefree for at
least r values of 1 ≤ k < n exist? Is this density > 0?

Erdős and Graham [ErGr80, p.72] state they can prove that, for k fixed and large,
the density of n such that C(n,k) is squarefree is o_k(1). They can also prove
that there are infinitely many n such that C(n,k) is not squarefree for 1 ≤ k < n,
and expect that the density of such n is positive.

Resolved in the affirmative by the results of Granville and Ramaré [GrRa96], who
show that for each m, the density of the set of n such that C(n,k) is squarefree
for exactly 2m+2 values of k exists.
-/

/-- The upper density of A ⊆ ℕ. -/
noncomputable def upperDensity378 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- The lower density of A ⊆ ℕ. -/
noncomputable def lowerDensity378 (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- A set of natural numbers has natural density d. -/
def hasNaturalDensity378 (A : Set ℕ) (d : ℝ) : Prop :=
  upperDensity378 A = d ∧ lowerDensity378 A = d

/-- The number of values k with 1 ≤ k < n such that C(n,k) is squarefree. -/
noncomputable def squarefreeBinomCount378 (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => 0 < k ∧ Squarefree (Nat.choose n k))).card

/-- The set of n for which C(n,k) is squarefree for at least r values of 1 ≤ k < n. -/
def squarefreeBinomAtLeast378 (r : ℕ) : Set ℕ :=
  {n : ℕ | r ≤ squarefreeBinomCount378 n}

/--
Erdős Problem #378 [ErGr80, p.72]:
For every r ≥ 0, the natural density of the set of integers n for which C(n,k)
is squarefree for at least r values of 1 ≤ k < n exists and is positive.
-/
theorem erdos_problem_378 (r : ℕ) :
    ∃ d : ℝ, d > 0 ∧ hasNaturalDensity378 (squarefreeBinomAtLeast378 r) d :=
  sorry
