import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Set

/--
The set of coprime pairs (p, q) with q > 0 that approximate α within f(q)/q.
-/
def DuffinSchafferApprox (f : ℕ → ℕ) (α : ℝ) : Set (ℤ × ℕ) :=
  {pq | 0 < pq.2 ∧ Nat.Coprime (Int.natAbs pq.1) pq.2 ∧
    |α - (pq.1 : ℝ) / (pq.2 : ℝ)| < (f pq.2 : ℝ) / (pq.2 : ℝ)}

/--
Erdős Problem #999 (the Duffin-Schaeffer conjecture, now theorem):
For any function f : ℕ → ℕ, the property that for almost all α ∈ ℝ,
|α - p/q| < f(q)/q has infinitely many solutions with gcd(p,q) = 1,
is equivalent to the divergence of ∑ φ(q) · f(q) / q.

Proved by Koukoulopoulos and Maynard [KoMa20].
-/
theorem erdos_problem_999 :
  ∀ f : ℕ → ℕ,
    (∀ᵐ α : ℝ, (DuffinSchafferApprox f α).Infinite) ↔
    (¬ Summable fun q : ℕ => (Nat.totient q : ℝ) * (f q : ℝ) / (q : ℝ)) :=
  sorry
