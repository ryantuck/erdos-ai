-- [AI-Generated]: Erdős Problem 1101 — second-pass formalization
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem 1101

*Source:* [erdosproblems.com/1101](https://www.erdosproblems.com/1101) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
19 October 2025, captured 2026-03-09).

If $u = \{u_1 < u_2 < \cdots\}$ is a sequence of integers such that $(u_i, u_j) = 1$ for
all $i \neq j$ and $\sum 1/u_i < \infty$ then let $\{a_1 < a_2 < \cdots\}$ be the sequence
of integers which are not divisible by any of the $u_i$. For any $x$ define $t_x$ by
$u_1 \cdots u_{t_x} \le x < u_1 \cdots u_{t_x} u_{t_x + 1}$. We call such a sequence $u_i$
*good* if, for all $\epsilon > 0$, if $x$ is sufficiently large then
$\max_{a_k < x} (a_{k+1} - a_k) < (1 + \epsilon) t_x \prod_i (1 - 1/u_i)^{-1}$.
Is there a good sequence such that $u_n < n^{O(1)}$? Is there a good sequence such that
$u_n \le e^{o(n)}$? [Er81h, p.178]

Remarks on the source page:
* Erdős [Er81h] believed the answer to the first question is no and the second question
  is yes. He proved the existence of some good sequence (in which all the $u_i$ are
  primes) — see `erdos_1101.variants.exists_good`.
* An easy sieve argument proves that we always have, for any sequence $u$ with those
  properties, $\max_{a_k < x} (a_{k+1} - a_k) > (1 + o(1)) t_x \prod_i (1 - 1/u_i)^{-1}$
  — see `erdos_1101.variants.sieve_lower_bound`. Good sequences are exactly those for
  which this trivial lower bound is asymptotically sharp.
* The strong form of Problem #208 asks whether $u_i = p_i^2$, the sequence of prime
  squares (whose sifted sequence is the squarefree numbers), is good. Not formalized here
  (it would need the prime enumeration, a construct absent from this file).

Tags: number theory. OEIS: none listed. The page records an upstream formalised statement
(google-deepmind/formal-conjectures); this file is independent of it.

## Encoding notes

* The source is 1-indexed ($u_1 < u_2 < \cdots$); here `u : ℕ → ℕ` is 0-indexed, so
  `u n` is $u_{n+1}$. Polynomial and $e^{o(n)}$ growth are both invariant under this
  shift, so neither question is affected.
* `2 ≤ u i` is made explicit: $u_i = 1$ would sieve out every integer (and make the
  factor $(1 - 1/u_i)^{-1}$ undefined), so the source implicitly excludes it.
* The two theorems state Erdős's *conjectured* answers as direct assertions (this raw
  corpus has no `answer()` elaborator). For Question 1 that is the negation of the asked
  existence statement; for Question 2 it is the asked statement itself. In `answer()`
  form they would read `answer(sorry) ↔ ∃ ud, IsGoodSeq ud ∧ ∃ C, ∀ᶠ n, u n < n ^ C`
  and `answer(sorry) ↔ ∃ ud, IsGoodSeq ud ∧ Tendsto (log (u n) / n) atTop (𝓝 0)`.

## References

* [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number
  theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.
  (Recovered from the original pipeline's fetch of `erdosproblems.com/latex/18`, which
  cites the same key; the volume/series is not in that extraction. Other glosses of this
  key found elsewhere in this repository's logs — "Some applications of graph theory and
  combinatorial methods to number theory and geometry", "Some problems and results in
  number theory" — are wrong for this key.)
-/

open Nat Filter Real

namespace Erdos1101

/--
A pairwise coprime sequence of integers ≥ 2 with convergent reciprocal sum.
We model this as a function `u : ℕ → ℕ` where `u` is strictly increasing,
all values are ≥ 2, pairwise coprime, and ∑ 1/u(i) converges.
-/
structure GoodSeqData where
  u : ℕ → ℕ
  strictMono : StrictMono u
  ge_two : ∀ i, 2 ≤ u i
  pairwiseCoprime : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
  summable_recip : Summable (fun i => (1 : ℝ) / (u i : ℝ))

/--
The "sifted" set: the positive integers not divisible by any u(i) — the source's
sequence $a_1 < a_2 < \cdots$ (note $a_1 = 1$, since every u(i) ≥ 2).
-/
def siftedSet (ud : GoodSeqData) : Set ℤ :=
  {a : ℤ | 0 < a ∧ ∀ i, ¬((ud.u i : ℤ) ∣ a)}

/--
The partial product u(0) * u(1) * ... * u(n-1).
-/
def partialProd (ud : GoodSeqData) : ℕ → ℕ
  | 0 => 1
  | n + 1 => partialProd ud n * ud.u n

/--
The partial products of a sequence with all terms ≥ 2 grow without bound.
-/
theorem partialProd_unbounded (ud : GoodSeqData) (x : ℕ) :
    ∃ n, x < partialProd ud n := by
  induction x with
  | zero => exact ⟨1, by simp [partialProd]; linarith [ud.ge_two 0]⟩
  | succ x ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      unfold partialProd
      have h2 := ud.ge_two n
      nlinarith⟩

/--
t_x is the largest t such that u(0)*...*u(t-1) ≤ x.

For `x ≥ 1` this is exactly the source's $t_x$: if `n` is the least index with
`x < partialProd ud n` then `n ≥ 1` and `partialProd ud (n - 1) ≤ x < partialProd ud n`,
i.e. $u_1 \cdots u_{t_x} \le x < u_1 \cdots u_{t_x + 1}$ with $t_x = n - 1$. For `x = 0`
the source's $t_x$ is undefined and this returns the junk value `0`, which is invisible
to every `atTop` statement below.
-/
noncomputable def tOfX (ud : GoodSeqData) (x : ℕ) : ℕ :=
  Nat.find (partialProd_unbounded ud x) - 1

/--
The source's $\max_{a_k < x} (a_{k+1} - a_k)$: the largest gap `b - a` between
consecutive sifted integers `a < b` whose *left* endpoint satisfies `a < x`. The gap
straddling `x` (from the last sifted integer below `x` to the next one) is included,
exactly as in the source. The set is finite for each `x`, so `sSup` is its maximum
(and `0` when it is empty, i.e. `x ≤ 1`).

(The first-pass file used `b ≤ x` instead of `a < x`, which drops the straddling gap —
e.g. for the prime squares it gives `1` instead of `2` at `x = 4`. The two conventions
give the same notion of `IsGoodSeq`: the old one is weaker pointwise, and conversely its
goodness bound forces all gaps up to `y` to be `O(log y)`, so the straddling gap at `x`
ends before `2x`, where `tOfX` has grown by at most one, and `t_x → ∞`. The main theorems
therefore have the same meaning under either convention; `a < x` is used because the
sieve lower bound below is only literally true for the source's version.)
-/
noncomputable def maxGap (ud : GoodSeqData) (x : ℕ) : ℕ :=
  sSup {g : ℕ | ∃ a ∈ siftedSet ud, ∃ b ∈ siftedSet ud,
    a < b ∧ a < (x : ℤ) ∧ g = (b - a).toNat ∧
    ∀ c ∈ siftedSet ud, a < c → c < b → False}

/--
The infinite product ∏(1 - 1/u(i))⁻¹, i.e., ∏ u(i)/(u(i)-1).
We define the partial products and take their supremum. Every factor is > 1 and the
partial products are bounded because ∑ 1/u(i) converges, so the supremum is the value
of the (convergent) infinite product.
-/
noncomputable def inverseProd (ud : GoodSeqData) : ℝ :=
  ⨆ n, ∏ i ∈ Finset.range n, ((ud.u i : ℝ) / ((ud.u i : ℝ) - 1))

/--
A sequence is "good" if for all ε > 0, for sufficiently large x,
the maximum gap among sifted integers below x is
< (1 + ε) * t_x * ∏(1 - 1/u_i)⁻¹.
-/
def IsGoodSeq (ud : GoodSeqData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
    (maxGap ud x : ℝ) < (1 + ε) * (tOfX ud x : ℝ) * inverseProd ud

/-- Erdős Problem #1101, Question 1 (OPEN) [Er81h, p.178]:

Is there a good sequence u such that u(n) < n^{O(1)}?

Erdős believed the answer is NO: there is no good sequence with
polynomial growth. That is, for every C > 0 and every good sequence,
u(n) > n^C for infinitely many n.

This states Erdős's conjectured answer, i.e. the *negation* of the asked
existence statement; proving it answers the question "no", refuting it answers
"yes". (`¬ ∃ C, ∀ᶠ n, u n < n ^ C` is equivalent to `∀ C > 0, ∃ᶠ n, n ^ C < u n`.) -/
theorem erdos_1101_no_polynomial_good_seq :
    ∀ ud : GoodSeqData, IsGoodSeq ud →
      ∀ C : ℝ, 0 < C → ∃ᶠ (n : ℕ) in atTop, (n : ℝ) ^ C < (ud.u n : ℝ) :=
  sorry

/-- Erdős Problem #1101, Question 2 (OPEN) [Er81h, p.178]:

Is there a good sequence u such that u(n) ≤ e^{o(n)}?

Erdős believed the answer is YES. That is, there exists a good sequence
such that log(u(n))/n → 0. (Since u(n) ≥ 2, `log (u n) > 0`, so
`u n ≤ exp (o(n))` is equivalent to `log (u n) / n → 0`.) -/
theorem erdos_1101_subexponential_good_seq :
    ∃ ud : GoodSeqData, IsGoodSeq ud ∧
      Tendsto (fun n => Real.log (ud.u n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  sorry

/-- Erdős [Er81h] proved that good sequences exist (his example has every u(i) prime;
only existence is stated here). -/
theorem erdos_1101.variants.exists_good :
    ∃ ud : GoodSeqData, IsGoodSeq ud :=
  sorry

/-- The easy sieve lower bound recorded on the source page: for *every* admissible
sequence, $\max_{a_k < x} (a_{k+1} - a_k) > (1 + o(1)) t_x \prod_i (1 - 1/u_i)^{-1}$,
i.e. for every ε > 0 the maximal gap eventually exceeds (1 - ε) t_x ∏(1 - 1/u_i)⁻¹.
(Proof sketch: with t = t_x, choose residues for u(0), …, u(t-1) covering an interval of
length (1 - ε) t ∏(1 - 1/u_i)⁻¹ and realize them by the Chinese remainder theorem below
u(0)⋯u(t-1) ≤ x; the covered interval then lies inside a gap whose left endpoint is < x.) -/
theorem erdos_1101.variants.sieve_lower_bound (ud : GoodSeqData) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
      (1 - ε) * (tOfX ud x : ℝ) * inverseProd ud < (maxGap ud x : ℝ) :=
  sorry

end Erdos1101
