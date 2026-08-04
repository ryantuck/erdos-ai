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

Status: OPEN (erdosproblems.com/1055, page captures accessed 2026-02-22 and
2026-03-06 agree).

A classification due to Erdős and Selfridge. It is easy to prove that the number
of primes $\leq n$ in class $r$ is at most $n^{o(1)}$. The sequence $p_r$ begins
$2, 13, 37, 73, 1021$ (A005113 in the OEIS). Erdős thought $p_r^{1/r} \to
\infty$, while Selfridge thought it quite likely to be bounded.

A similar question can be asked replacing $p+1$ with $p-1$ (not formalized here:
it needs a parallel classification with its own degenerate case at $p = 2$).

This is problem A18 in Guy's collection [Gu04]. An upstream formalization exists
at google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1055.lean`),
which is the authoritative artifact for this problem; the statements below are
semantically aligned with it.

References:

[Er77] Erdős, P. (1977). [Source of the problem per erdosproblems.com/1055.
Bibliographic stub: full details were not recoverable from the archived page
captures — the site's `/latex/1055` bibliography was never fetched. Sibling
files in this corpus associate a same-era key with *Problems in number theory
and combinatorics*, Proc. Sixth Manitoba Conf. Numerical Math., 35–58, but
under inconsistent year keys, so no details are asserted here.]

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004),
xviii+437. Problem A18.
-/

/-- `erdos1055_classAtMost r p` holds when the Erdős–Selfridge class of `p` is
at most `r`: every prime factor in the recursion tree rooted at `p+1` resolves
to $\{2, 3\}$ within `r` levels. `erdos1055_classAtMost 0 p` is `False`, since
every prime has class at least $1$. The predicate is monotone in `r` (a prime
of class $\leq r$ also has class $\leq r+1$, because $2$ and $3$ themselves
have class $1$). For non-prime `p` the predicate is not meaningful on its own;
every use below conjoins `Nat.Prime p`. -/
def erdos1055_classAtMost : ℕ → ℕ → Prop
  | 0, _ => False
  | 1, p => (p + 1).primeFactors ⊆ {2, 3}
  | r + 2, p => ∀ q ∈ (p + 1).primeFactors, erdos1055_classAtMost (r + 1) q

/-- `erdos1055_hasClass r p` holds when the Erdős–Selfridge class of `p` is
exactly `r`: the class is at most `r` but not at most `r - 1`. A prime $p$ has
class $1$ iff every prime factor of $p+1$ is $2$ or $3$; it has class $r \ge 2$
iff every prime factor of $p+1$ has class $\le r-1$ with equality for at least
one factor. (The ℕ-subtraction `r - 1` is harmless: the conjunct `1 ≤ r` guards
it, and at `r = 1` the last conjunct is `¬False`, i.e. trivially true, as
intended.) -/
def erdos1055_hasClass (r p : ℕ) : Prop :=
  1 ≤ r ∧ erdos1055_classAtMost r p ∧ ¬erdos1055_classAtMost (r - 1) p

/-- The set of primes in Erdős–Selfridge class `r`. Empty for `r = 0`. -/
def erdos1055_classSet (r : ℕ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ erdos1055_hasClass r p}

/-- The least prime in class `r`, i.e. $p_r$. By Mathlib's `sInf` convention on
`ℕ` this is the junk value `0` if class `r` should be empty (whether every
class is nonempty is itself part of the problem; see
`erdos_problem_1055_exists_prime_in_class`). -/
noncomputable def erdos1055_leastPrimeInClass (r : ℕ) : ℕ :=
  sInf (erdos1055_classSet r)

/--
Erdős Problem #1055 (part 1, OPEN) [Er77]:

Are there infinitely many primes in each class $r \geq 1$? This statement
asserts the "yes" direction of the open question, following the upstream
formalization.
-/
theorem erdos_problem_1055_infinitely_many (r : ℕ) (hr : 1 ≤ r) :
    Set.Infinite (erdos1055_classSet r) :=
  sorry

/--
Erdős Problem #1055 (part 2, OPEN) [Er77] (Erdős' conjecture):

Erdős conjectured that $p_r^{1/r} \to \infty$ as $r \to \infty$, where $p_r$
is the least prime in class $r$. Selfridge thought it quite likely to be
bounded (see `erdos_problem_1055_selfridge_bounded` for that direction; the two
statements are mutually exclusive and each records one stated belief).
-/
theorem erdos_problem_1055_growth :
    Tendsto (fun r => (erdos1055_leastPrimeInClass r : ℝ) ^ ((r : ℝ)⁻¹))
      atTop atTop :=
  sorry

/--
Erdős Problem #1055 (part 2, OPEN) [Er77] (Selfridge's conjecture):

Selfridge thought it quite likely that $p_r^{1/r}$ is bounded, where $p_r$ is
the least prime in class $r$. This is the direction opposite to
`erdos_problem_1055_growth`.
-/
theorem erdos_problem_1055_selfridge_bounded :
    ∃ M : ℝ, ∀ r : ℕ, 1 ≤ r →
      (erdos1055_leastPrimeInClass r : ℝ) ^ ((r : ℝ)⁻¹) ≤ M :=
  sorry

/--
Erdős Problem #1055 (auxiliary):

Every class $r \geq 1$ contains at least one prime, so that $p_r$ is
well-defined. This is implicit in the problem statement ("If $p_r$ is the
least prime in class $r$ ...") and is stated in the upstream formalization
(as `exists_p`, marked there as an exercise rather than a research problem).
-/
theorem erdos_problem_1055_exists_prime_in_class (r : ℕ) (hr : 1 ≤ r) :
    (erdos1055_classSet r).Nonempty :=
  sorry

end
