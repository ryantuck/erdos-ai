import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

noncomputable section

/-!
# Erdős Problem #1055

A prime $p$ is in class $1$ if the only prime divisors of $p+1$ are $2$ or $3$.
In general, a prime $p$ is in class $r$ if every prime factor of $p+1$ is in
some class $\leq r-1$, with equality for at least one prime factor.

Are there infinitely many primes in each class? If $p_r$ is the least prime in
class $r$, then how does $p_r^{1/r}$ behave?

A classification due to Erdős and Selfridge. The sequence $p_r$ begins
$2, 13, 37, 73, 1021$ (A005113 in the OEIS). Erdős thought $p_r^{1/r} \to
\infty$, while Selfridge thought it quite likely to be bounded.
-/

/-- The Erdős-Selfridge class of a prime, defined recursively.
A prime p has class 1 if every prime factor of p+1 is 2 or 3.
A prime p has class r (for r ≥ 2) if every prime factor of p+1
has class ≤ r-1 and at least one has class exactly r-1.
For non-primes, we define the class to be 0. -/
noncomputable def erdos1055_primeClass : ℕ → ℕ
  | p =>
    if _hp : Nat.Prime p then
      let factorClasses := (Nat.primeFactors (p + 1)).image (fun q =>
        if q = 2 ∨ q = 3 then 0
        else erdos1055_primeClass q)
      if factorClasses = ∅ then 0
      else factorClasses.sup id + 1
    else 0
termination_by p => p
decreasing_by all_goals sorry

/-- The set of primes in Erdős-Selfridge class r. -/
def erdos1055_classSet (r : ℕ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ erdos1055_primeClass p = r}

/-- The least prime in class r, if it exists. -/
noncomputable def erdos1055_leastPrimeInClass (r : ℕ) : ℕ :=
  sInf (erdos1055_classSet r)

/--
Erdős Problem #1055 (part 1, OPEN):

Are there infinitely many primes in each class r ≥ 1?
-/
theorem erdos_problem_1055_infinitely_many (r : ℕ) (hr : 1 ≤ r) :
    Set.Infinite (erdos1055_classSet r) :=
  sorry

/--
Erdős Problem #1055 (part 2, OPEN):

Erdős conjectured that $p_r^{1/r} \to \infty$ as $r \to \infty$, where $p_r$
is the least prime in class $r$. Selfridge thought it quite likely to be bounded.
-/
theorem erdos_problem_1055_growth :
    Tendsto (fun r => (erdos1055_leastPrimeInClass r : ℝ) ^ ((r : ℝ)⁻¹))
      atTop atTop :=
  sorry

end
