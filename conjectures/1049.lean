import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational

open scoped Topology

/-!
# Erdős Problem #1049

Let t > 1 be a rational number. Is

  ∑_{n=1}^∞ 1/(t^n - 1) = ∑_{n=1}^∞ τ(n)/t^n

irrational, where τ(n) counts the divisors of n?

A conjecture of Chowla. Erdős [Er48] proved that this is true if t ≥ 2 is an
integer.

Status: OPEN (erdosproblems.com/1049, page edition 28 September 2025). The two
series are equal by the classical Lambert-series identity ∑_{n≥1} x^n/(1-x^n)
= ∑_{n≥1} τ(n) x^n with x = 1/t, valid for t > 1; this file formalizes the
left-hand (Lambert) form. The authoritative upstream formalization lives in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1049.lean)
and is not present in this repository.

[Er88c] Erdős, P., *On the irrationality of certain series: problems and
results*. New advances in transcendence theory (Durham, 1986) (1988), 102-109.

[Er48] Erdős, P., *On arithmetical properties of Lambert series*. J. Indian
Math. Soc. (N.S.) (1948), 63-66.
-/

/--
Erdős Problem #1049 [Er88c,p.102]:

Let t > 1 be a rational number. Is
  ∑_{n=1}^∞ 1/(t^n - 1) = ∑_{n=1}^∞ τ(n)/t^n
irrational, where τ(n) counts the divisors of n?

A conjecture of Chowla. Erdős [Er48] proved that this is true if t ≥ 2 is an
integer.

The problem is OPEN; this raw statement asserts the conjectured ("yes")
direction, for the Lambert-series (left-hand) form of the sum.
-/
theorem erdos_problem_1049
    (t : ℚ) (ht : 1 < t) :
    Irrational (∑' (n : ℕ), (1 : ℝ) / ((t : ℝ) ^ (n + 1) - 1)) :=
  sorry

/--
Erdős [Er48] proved the integer case of Problem #1049: for every integer
t ≥ 2, the sum ∑_{n=1}^∞ 1/(t^n - 1) is irrational. (Solved.)
-/
theorem erdos_problem_1049.variants.integer_case
    (t : ℤ) (ht : 2 ≤ t) :
    Irrational (∑' (n : ℕ), (1 : ℝ) / ((t : ℝ) ^ (n + 1) - 1)) :=
  sorry
