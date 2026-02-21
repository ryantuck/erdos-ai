import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter

/-- Count the number of representations of `m` as `a i + a j` with `i < j < n`. -/
def ulamRepCount342 (a : ℕ → ℕ) (n m : ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun p : Fin n × Fin n => p.1.val < p.2.val ∧ a p.1.val + a p.2.val = m)
    Finset.univ)

/-- The Ulam sequence: `a(0) = 1`, `a(1) = 2`, and for each `n ≥ 2`, `a(n)` is the
    least integer greater than `a(n-1)` that has exactly one representation as
    `a(i) + a(j)` with `i < j < n`. (OEIS A002858) -/
def IsUlamSequence342 (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ a 1 = 2 ∧
  ∀ n, 2 ≤ n →
    a (n - 1) < a n ∧
    ulamRepCount342 a n (a n) = 1 ∧
    ∀ m, a (n - 1) < m → m < a n → ulamRepCount342 a n m ≠ 1

/-- The upper density of A ⊆ ℕ:
    d*(A) = limsup_{N→∞} |A ∩ {0, 1, ..., N-1}| / N -/
noncomputable def upperDensity342 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #342, Part 1 [ErGr80, p.53]:

A problem of Ulam. With a₁ = 1 and a₂ = 2 let aₙ₊₁ for n ≥ 2 be the least
integer > aₙ which can be expressed uniquely as aᵢ + aⱼ for i < j ≤ n.
The sequence is 1, 2, 3, 4, 6, 8, 11, 13, 16, 18, 26, 28, …

Do infinitely many pairs a, a + 2 occur in the sequence?
-/
theorem erdos_problem_342_pairs :
    ∀ a : ℕ → ℕ, IsUlamSequence342 a →
      Set.Infinite {n : ℕ | ∃ m, a m = a n + 2} :=
  sorry

/--
Erdős Problem #342, Part 2 [ErGr80, p.53]:

Does the Ulam sequence eventually have periodic differences?
That is, do there exist N and p > 0 such that
a(n + p + 1) - a(n + p) = a(n + 1) - a(n) for all n ≥ N?
-/
theorem erdos_problem_342_periodic :
    ∀ a : ℕ → ℕ, IsUlamSequence342 a →
      ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n →
        a (n + p + 1) - a (n + p) = a (n + 1) - a n :=
  sorry

/--
Erdős Problem #342, Part 3 [ErGr80, p.53]:

Is the (upper) density of the Ulam sequence equal to 0?
-/
theorem erdos_problem_342_density :
    ∀ a : ℕ → ℕ, IsUlamSequence342 a →
      upperDensity342 (Set.range a) = 0 :=
  sorry
