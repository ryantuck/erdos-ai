import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.Basic

open Filter Set

/--
A set S ⊆ ℕ is **complete** if every sufficiently large natural number can be
written as a sum of distinct elements of S.
-/
def IsComplete346 (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ F : Finset ℕ, ↑F ⊆ S ∧ F.sum id = n

/--
A strictly increasing sequence a : ℕ → ℕ (representing {a 0 < a 1 < a 2 < ⋯})
is **subcomplete-robust** if removing any finite subset of its range leaves a
complete set, but removing any infinite subset does not.
-/
def SubcompleteRobust (a : ℕ → ℕ) : Prop :=
  (∀ B : Finset ℕ, IsComplete346 (range a \ ↑B)) ∧
  (∀ B : Set ℕ, B ⊆ range a → B.Infinite → ¬IsComplete346 (range a \ B))

/--
Erdős Problem #346 [ErGr80, p.57]:

Let A = {a₁ < a₂ < ⋯} be a set of integers satisfying:
  (1) A \ B is complete for any finite subset B, and
  (2) A \ B is not complete for any infinite subset B.

Is it true that if a_{n+1}/a_n ≥ 1 + ε for some ε > 0 and all n, then
  lim_{n→∞} a_{n+1}/a_n = (1 + √5)/2?

Graham showed that aₙ = Fₙ - (-1)ⁿ (where Fₙ is the nth Fibonacci number)
has these properties. Erdős and Graham remark that if a_{n+1}/a_n > (1+√5)/2
then the second property is automatically satisfied.
-/
theorem erdos_problem_346
    (a : ℕ → ℕ)
    (ha_strict : StrictMono a)
    (ha_robust : SubcompleteRobust a)
    (ε : ℝ) (hε : 0 < ε)
    (ha_growth : ∀ n : ℕ, (a (n + 1) : ℝ) / (a n : ℝ) ≥ 1 + ε) :
    Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (nhds ((1 + Real.sqrt 5) / 2)) :=
  sorry
