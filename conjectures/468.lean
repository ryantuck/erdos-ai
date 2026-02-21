import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter

noncomputable section

/-!
# Erdős Problem #468

For any $n$ let $D_n$ be the set of partial sums $d_1, d_1+d_2, d_1+d_2+d_3, \ldots$
where $1 < d_1 < d_2 < \cdots$ are the divisors of $n$.

If $f(N)$ is the minimal $n$ such that $N \in D_n$, is it true that $f(N) = o(N)$?
Perhaps just for almost all $N$?
-/

/-- Prefix sums of a list with accumulator. Returns [acc+a₁, acc+a₁+a₂, ...]. -/
def erdos468_prefixSums : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: as, acc => (acc + a) :: erdos468_prefixSums as (acc + a)

/-- D_n: the set of partial sums of the divisors of n that are greater than 1,
    taken in increasing order. -/
def erdos468_D (n : ℕ) : Finset ℕ :=
  (erdos468_prefixSums ((n.divisors.filter (1 < ·)).sort (· ≤ ·)) 0).toFinset

/-- f(N): the minimal n such that N ∈ D_n. -/
noncomputable def erdos468_f (N : ℕ) : ℕ :=
  sInf {n : ℕ | N ∈ erdos468_D n}

/--
Erdős Problem #468, strong form [ErGr80]:

If f(N) is the minimal n such that N ∈ D_n, then f(N) = o(N).
-/
theorem erdos_problem_468_strong :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (erdos468_f N : ℝ) < ε * (N : ℝ) :=
  sorry

/--
Erdős Problem #468, weak form [ErGr80]:

f(N) = o(N) for almost all N. Formalized as: for any ε > 0, the density of
{N ≤ x : f(N) ≥ ε·N} tends to 0 as x → ∞.
-/
theorem erdos_problem_468_weak :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun N =>
          (erdos468_f N : ℝ) ≥ ε * (N : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) :=
  sorry

end
