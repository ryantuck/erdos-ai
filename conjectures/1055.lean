import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Filter

noncomputable section

/-!
# Erdős Problem #1055

A prime p is in class 1 if the only prime divisors of p+1 are 2 or 3.
In general, a prime p is in class r if every prime factor of p+1 is in some
class ≤ r-1, with equality for at least one prime factor.

A classification due to Erdős and Selfridge. The sequence p_r of least primes
in class r begins 2, 13, 37, 73, 1021 (A005113 in the OEIS).

Are there infinitely many primes in each class? If p_r is the least prime
in class r, then how does p_r^{1/r} behave? Erdős thought p_r^{1/r} → ∞,
while Selfridge thought it quite likely to be bounded.
-/

/-- `classAtMost r p` holds when the Erdős-Selfridge class of p is at most r.
    Equivalently, all prime factors in the "tower" rooted at p+1 resolve to
    {2, 3} within r levels. -/
def classAtMost : ℕ → ℕ → Prop
  | 0, _ => False
  | 1, p => (p + 1).primeFactors ⊆ {2, 3}
  | r + 2, p => ∀ q ∈ (p + 1).primeFactors, classAtMost (r + 1) q

/-- `erdosSelfridgeClass r p` holds when p has Erdős-Selfridge class exactly r.
    A prime p is in class 1 if the only prime divisors of p+1 are 2 or 3.
    A prime p is in class r (r ≥ 2) if every prime factor of p+1 is in some
    class ≤ r-1, with at least one factor not in class ≤ r-2. -/
def erdosSelfridgeClass (r : ℕ) (p : ℕ) : Prop :=
  r ≥ 1 ∧ classAtMost r p ∧ ¬classAtMost (r - 1) p

/-- The least prime of Erdős-Selfridge class r. -/
noncomputable def leastPrimeInClass (r : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ erdosSelfridgeClass r p}

/--
Erdős Problem #1055, Part 1 [Er77]:

Are there infinitely many primes in each Erdős-Selfridge class?
-/
theorem erdos_problem_1055_infinitely_many (r : ℕ) (hr : r ≥ 1) :
    {p : ℕ | p.Prime ∧ erdosSelfridgeClass r p}.Infinite :=
  sorry

/--
Erdős Problem #1055, Part 2a [Er77] (Erdős' conjecture):

If p_r is the least prime in Erdős-Selfridge class r, then p_r^{1/r} → ∞.
-/
theorem erdos_problem_1055_erdos_conjecture :
    Filter.Tendsto (fun r : ℕ => (leastPrimeInClass r : ℝ) ^ ((1 : ℝ) / (r : ℝ)))
      Filter.atTop Filter.atTop :=
  sorry

/--
Erdős Problem #1055, Part 2b [Er77] (Selfridge's conjecture):

If p_r is the least prime in Erdős-Selfridge class r, then p_r^{1/r} is bounded.
-/
theorem erdos_problem_1055_selfridge_conjecture :
    ∃ M : ℝ, ∀ r : ℕ, r ≥ 1 →
      (leastPrimeInClass r : ℝ) ^ ((1 : ℝ) / (r : ℝ)) ≤ M :=
  sorry

end
