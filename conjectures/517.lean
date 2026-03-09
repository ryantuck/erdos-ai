import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Basic

open Filter Set

/--
Erdős Problem #517 [Er61,p.250]:

Let f(z) = ∑_{k=1}^∞ a_k z^{n_k} be an entire function (with a_k ≠ 0 for all
k ≥ 1). Is it true that if n_k/k → ∞ then f(z) assumes every value infinitely
often?

A conjecture of Fejér and Pólya.
-/
theorem erdos_problem_517
    (n : ℕ → ℕ) (a : ℕ → ℂ)
    (hn_strict : StrictMono n)
    (ha_ne : ∀ k, a k ≠ 0)
    (h_entire : ∀ z : ℂ, Summable (fun k => a k * z ^ n k))
    (h_gap : Tendsto (fun k => (n k : ℝ) / (k : ℝ)) atTop atTop) :
    ∀ w : ℂ, Set.Infinite {z : ℂ | ∑' k, a k * z ^ n k = w} :=
  sorry
