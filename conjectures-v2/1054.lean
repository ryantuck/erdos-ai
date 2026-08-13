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
# Erdős Problem #1054

Let $f(n)$ be the minimal integer $m$ such that $n$ is the sum of the $k$
smallest divisors of $m$ for some $k \geq 1$.

Is it true that $f(n) = o(n)$? Or is this true only for almost all $n$,
and $\limsup f(n)/n = \infty$?

A question of Erdős reported in problem B2 of Guy's collection [Gu04].
Status on erdosproblems.com/1054: OPEN (page edition 06 December 2025,
accessed 2026-03-06).

The strong claim $f(n) = o(n)$ was disproved by Tao in the comments to
Erdős problem [468], in which he proves that the upper density of
$\{n : f(n) \leq \delta n\}$ is $\ll \delta^2$. Note that this bound also
refutes the "almost all" alternative: if $f(n) = o(n)$ held on a set of
density $1$, then $\{n : f(n) \leq \delta n\}$ would have density $1$ for
every fixed $\delta > 0$, contradicting the $\ll \delta^2$ bound once
$\delta$ is small. The remaining open content of the problem is the final
alternative, whether $\limsup f(n)/n = \infty$.

The function $f(n)$ is undefined for $n = 2$ and $n = 5$ (this formalization
assigns such $n$ the junk value $f(n) = 0$, via `sInf ∅ = 0`), but is likely
well-defined for all $n \geq 6$, which would follow from a strong form of
Goldbach's conjecture. Classical results (almost-all binary Goldbach for
$n - 1$ even, Vinogradov's three-primes theorem for $n - 1$ odd, giving
$n = 1 + p + q$ resp. $n = 1 + p + q + r$ as a sum of the smallest divisors
of $pq$ resp. $pqr$) show unconditionally that the set of $n$ where $f$ is
undefined has natural density $0$; the negated theorems below use this fact
together with Tao's bound.

The sequence of values of $f(n)$ is given by A167485 in the OEIS.
See also Erdős problem [468] (formalized in this repository as
`conjectures/468.lean` / `deepmind/468.lean`), whose $f$ is the analogous
minimal $n$ with $N$ a partial sum of the divisors of $n$ that exceed $1$.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. 3rd ed.,
Springer (2004), xviii+437. Problem B2. (Bibliographic data from sibling
files in this repository carrying the same key, e.g. `deepmind/45.lean`;
the site's `/bibs/Gu04` payload was not captured in the session logs.)

Note: the authoritative upstream formalization of this problem lives in
google-deepmind/formal-conjectures (`FormalConjectures/ErdosProblems/1054.lean`,
linked from the problem page as "Formalised statement? Yes") and is not
present in this repository; this file is the local raw first-pass.
-/

/-- The sorted list of divisors of n in increasing order. -/
def erdos1054_sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Prefix sums of a list with accumulator. Returns [acc+a₁, acc+a₁+a₂, ...]. -/
def erdos1054_prefixSums : List ℕ → ℕ → List ℕ
  | [], _ => []
  | a :: as, acc => (acc + a) :: erdos1054_prefixSums as (acc + a)

/-- The set of values obtainable as sums of the k smallest divisors of n,
    for some k ≥ 1. Note `erdos1054_S 0 = ∅` (Mathlib's `Nat.divisors 0 = ∅`),
    so m = 0 never witnesses membership below. -/
def erdos1054_S (n : ℕ) : Finset ℕ :=
  (erdos1054_prefixSums (erdos1054_sortedDivisors n) 0).toFinset

/-- f(n): the minimal m such that n ∈ erdos1054_S m, i.e., n is the sum of
    the k smallest divisors of m for some k ≥ 1.

    Genuine values satisfy f(n) ≥ 1. When no such m exists (the source notes
    f is undefined for n = 2 and n = 5, and its well-definedness for all
    n ≥ 6 is itself open, following from a strong form of Goldbach's
    conjecture), `sInf` of the empty set returns the junk value 0; thus
    `erdos1054_f n = 0 ↔ f is undefined at n` (for n ≥ 1). -/
noncomputable def erdos1054_f (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ∈ erdos1054_S m}

/--
Erdős Problem #1054, strong form — DISPROVED by Tao (in the comments to
Erdős problem [468]): it is NOT the case that f(n) = o(n). Tao proves the
quantitative bound that the upper density of {n : f(n) ≤ δn} is ≪ δ²
(see `erdos_problem_1054_tao_density`), which is incompatible with
{n : f(n) < εn} being cofinite for small ε, since the set of n at which f
is undefined (junk value 0, counted by the inner statement as satisfying
f(n) < εn) has density 0 by classical almost-all Goldbach/Vinogradov results.

Stated in the true (negated) direction. NOTE: this fix is not compile-verified.
-/
theorem erdos_problem_1054_strong :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (erdos1054_f n : ℝ) < ε * (n : ℝ)) :=
  sorry

/--
Erdős Problem #1054, "almost all" form — also FALSE, by the same result of
Tao: if for every ε > 0 the density of {n ≤ x : f(n) ≥ εn} tended to 0, then
{n : f(n) ≤ εn} would have density 1 for each fixed ε > 0, contradicting
Tao's upper-density bound ≪ ε² once ε is small. (As above, the n at which f
is undefined carry junk value 0 and are excluded from the filtered set; that
set of n has density 0 by classical results, so the negation of the literal
Lean statement follows from Tao's bound.)

Stated in the true (negated) direction. NOTE: this fix is not compile-verified.
-/
theorem erdos_problem_1054 :
    ¬ (∀ ε : ℝ, 0 < ε →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          (erdos1054_f n : ℝ) ≥ ε * (n : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0)) :=
  sorry

/--
Tao's quantitative result (proved in the comments to Erdős problem [468],
quoted on the erdosproblems.com/1054 page): the upper density of
{n : f(n) ≤ δn} is ≪ δ². Formalized with an eventual counting bound, which
is equivalent to the limsup formulation up to the value of the constant C.
The conjunct `0 < erdos1054_f n` restricts to n where f is genuinely defined,
so the counted set is exactly {1 ≤ n ≤ x : f defined at n and f(n) ≤ δn},
free of junk values.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1054_tao_density :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        (((Finset.Icc 1 x).filter (fun n =>
          0 < erdos1054_f n ∧ (erdos1054_f n : ℝ) ≤ δ * (n : ℝ))).card : ℝ)
          ≤ C * δ ^ 2 * (x : ℝ) :=
  sorry

/--
Erdős Problem #1054, remaining OPEN part: is limsup f(n)/n = ∞? Encoded as:
for every C > 0 there are infinitely many n with f(n) > C·n. (Witnesses
automatically have f(n) > 0, hence f genuinely defined, so the junk value
does not enter.) This is the final alternative in the source's question,
stated in the direction suggested there; in styled question form it would be
`answer(sorry) ↔ …`.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1054_limsup :
    ∀ C : ℝ, 0 < C →
      ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ C * (n : ℝ) < (erdos1054_f n : ℝ) :=
  sorry

end
