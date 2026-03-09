import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Real
import Mathlib.Data.Real.Basic

open Set

noncomputable section

/--
The set of all triples (∑_{n∈A} 1/n, ∑_{n∈A} 1/(n+1), ∑_{n∈A} 1/(n+2))
where A ⊆ ℕ ranges over all infinite sets with ∑_{n∈A} 1/n < ∞.
-/
def erdos268Set : Set (ℝ × ℝ × ℝ) :=
  { p | ∃ (A : Set ℕ), A.Infinite ∧
    Summable (fun n : A => (1 : ℝ) / (n : ℝ)) ∧
    p = (∑' (n : A), (1 : ℝ) / (n : ℝ),
         ∑' (n : A), (1 : ℝ) / ((n : ℝ) + 1),
         ∑' (n : A), (1 : ℝ) / ((n : ℝ) + 2)) }

/--
Erdős Problem #268 [ErGr80,p.65] [Er88c,p.105]:

Let X ⊆ ℝ³ be the set of all points
  (∑_{n∈A} 1/n, ∑_{n∈A} 1/(n+1), ∑_{n∈A} 1/(n+2))
as A ⊆ ℕ ranges over all infinite sets with ∑_{n∈A} 1/n < ∞.
Does X contain an open set?

The answer is yes, proved by Kovač [Ko24].
-/
theorem erdos_problem_268 : (interior erdos268Set).Nonempty := sorry

end
