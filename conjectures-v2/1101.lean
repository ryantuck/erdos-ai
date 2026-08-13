import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

open Nat Filter Real

/-!
# Erdős Problem #1101

If $u = \{u_1 < u_2 < \cdots\}$ is a sequence of integers such that
$(u_i, u_j) = 1$ for all $i \neq j$ and $\sum \frac{1}{u_i} < \infty$ then let
$\{a_1 < a_2 < \cdots\}$ be the sequence of integers which are not divisible by
any of the $u_i$. For any $x$ define $t_x$ by
$$u_1 \cdots u_{t_x} \leq x < u_1 \cdots u_{t_x} u_{t_x + 1}.$$
We call such a sequence $u_i$ *good* if, for all $\epsilon > 0$, if $x$ is
sufficiently large then
$$\max_{a_k < x} (a_{k+1} - a_k) < (1+\epsilon) t_x
  \prod_i \left(1 - \frac{1}{u_i}\right)^{-1}.$$
Is there a good sequence such that $u_n < n^{O(1)}$?
Is there a good sequence such that $u_n \leq e^{o(n)}$?

Status on erdosproblems.com/1101: OPEN (page edition 19 October 2025, accessed
2026-03-09). Source citation on the page: [Er81h, p.178].

Erdős [Er81h] believed the answer to the first question is no and the second
question is yes. He proved the existence of some good sequence (in which all
the $u_i$ are primes). An easy sieve argument proves that we always have, for
any sequence $u$ with those properties,
$$\max_{a_k < x} (a_{k+1} - a_k) > (1+o(1)) t_x
  \prod_i \left(1 - \frac{1}{u_i}\right)^{-1}.$$
The strong form of erdosproblems.com problem [208] (gaps between squarefree
numbers, cf. `conjectures/208.lean` in this repo) is asking whether
$u_i = p_i^2$, the sequence of prime squares, is good — the integers not
divisible by any prime square are exactly the squarefree numbers.

Both questions are OPEN yes/no questions; following this corpus's raw-file
convention (cf. `conjectures/208.lean`) each is encoded as a direct assertion
of Erdős's believed direction, with the belief stated explicitly in the
theorem docstrings.

The hypothesis $u_i \geq 2$ made explicit in `GoodSeqData` is forced by the
source's own formulas: $u_i = 1$ would make the sifted sequence empty and
$(1 - 1/u_i)^{-1}$ undefined.

Tags: number theory.

References (honest stub; the site loads full bibliographic data via separate
`/bibs/` requests that were not captured in the session logs — journal data
below is carried over from sibling files in this repo
(`deepmind/deepmind/18.lean`, `deepmind/deepmind/840.lean`) and the
`/latex/1100` extraction recovered for fable-review/1100, which cite the same
key; volume number unknown):
- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative
  number theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981),
  171–182. This problem: p. 178.

Note: the problem page links "Formalised statement? Yes" to the authoritative
upstream formalization in google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/1101.lean`), which is not present in this
repository (and whose content was not recoverable from the session logs);
this file is the local raw first-pass with review fixes applied.

NOTE: the docstring enrichments and the two added variants below are from the
fable review of 2026-08-13 and are not compile-verified (the review container
cannot run `lake build`).
-/

namespace Erdos1101

/--
A pairwise coprime sequence of integers ≥ 2 with convergent reciprocal sum.
We model this as a function `u : ℕ → ℕ` where `u` is strictly increasing,
all values are ≥ 2, pairwise coprime, and ∑ 1/u(i) converges.

(The source says "a sequence of integers"; the values must be ≥ 2 for the
problem to be non-degenerate — see the module docstring. Lean index `i`
corresponds to the source's 1-based index `i + 1`.)
-/
structure GoodSeqData where
  u : ℕ → ℕ
  strictMono : StrictMono u
  ge_two : ∀ i, 2 ≤ u i
  pairwiseCoprime : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
  summable_recip : Summable (fun i => (1 : ℝ) / (u i : ℝ))

/--
The "sifted" set: positive integers not divisible by any u(i).
(The source's sequence a_1 < a_2 < ⋯; note 1 is always in this set, and the
set is infinite since the sifted density ∏(1 - 1/u_i) is positive.)
-/
def siftedSet (ud : GoodSeqData) : Set ℤ :=
  {a : ℤ | 0 < a ∧ ∀ i, ¬((ud.u i : ℤ) ∣ a)}

/--
The partial product u(0) * u(1) * ... * u(n-1), i.e. the source's
u_1 ⋯ u_n. Strictly increasing in `n` since every factor is ≥ 2.
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
t_x is the largest t such that u(0)*...*u(t-1) ≤ x; equivalently the t with
u_1 ⋯ u_t ≤ x < u_1 ⋯ u_t u_{t+1} as in the source (exact for every x ≥ 1,
since `partialProd` is strictly increasing and `partialProd 0 = 1 ≤ x`).

Degenerate case: at x = 0 the least n with x < partialProd n is 0, and the ℕ
subtraction truncates to give `tOfX ud 0 = 0` (junk; the source's t_x is
undefined there). Harmless: `IsGoodSeq` only looks at x eventually.
Note t_x → ∞ as x → ∞ (each partial product is finite).
-/
noncomputable def tOfX (ud : GoodSeqData) (x : ℕ) : ℕ :=
  Nat.find (partialProd_unbounded ud x) - 1

/--
The max gap among sifted integers up to x: the supremum of b - a over pairs
a < b ≤ x of consecutive elements of `siftedSet` (no sifted element strictly
between). `sSup` of a set of ℕ; the set is bounded (every gap is ≤ x - 1), and
it is empty for small x (fewer than two sifted elements ≤ x), where `sSup ∅`
returns the junk value 0 — harmless under the eventual quantifier.

Windowing note: the source takes max_{a_k < x} (a_{k+1} - a_k), indexing gaps
by their *left* endpoint a_k < x (so the one gap bridging x is included),
whereas this definition requires the *right* endpoint b ≤ x (bridge excluded).
The two maxima can differ pointwise, but they define the same class of good
sequences in `IsGoodSeq`: the bridge gap ending at x' = a_{K+1} is controlled
by the windowed bound at x', and since consecutive partial products differ by
a factor ≥ 2, t_{x'} ≤ t_{2x} ≤ t_x + 1, which is absorbed into ε because
t_x → ∞. See fable-review/1101.md §A2 for the full argument.
-/
noncomputable def maxGap (ud : GoodSeqData) (x : ℕ) : ℕ :=
  sSup {g : ℕ | ∃ a ∈ siftedSet ud, ∃ b ∈ siftedSet ud,
    a < b ∧ b ≤ (x : ℤ) ∧ g = (b - a).toNat ∧
    ∀ c ∈ siftedSet ud, a < c → c < b → False}

/--
The infinite product ∏(1 - 1/u(i))⁻¹, i.e., ∏ u(i)/(u(i)-1).
We define the partial products and take their supremum: the partial products
are increasing (every factor > 1, as u(i) ≥ 2) and bounded above (since
∑ 1/u(i) < ∞ forces the product to converge), so the supremum is the true
value of the convergent infinite product — the junk value of an unbounded
real `iSup` cannot occur for a `GoodSeqData`. (Mathlib's `tprod`/`Multipliable`
would be the idiomatic encoding; the `iSup` form is equivalent here.)
-/
noncomputable def inverseProd (ud : GoodSeqData) : ℝ :=
  ⨆ n, ∏ i ∈ Finset.range n, ((ud.u i : ℝ) / ((ud.u i : ℝ) - 1))

/--
A sequence is "good" if for all ε > 0, for sufficiently large x,
the maximum gap among sifted integers up to x is
< (1 + ε) * t_x * ∏(1 - 1/u_i)⁻¹.

(Faithful to the source's definition of good; see the windowing note on
`maxGap` — the b ≤ x window provably defines the same class of good
sequences as the source's a_k < x indexing.)
-/
def IsGoodSeq (ud : GoodSeqData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
    (maxGap ud x : ℝ) < (1 + ε) * (tOfX ud x : ℝ) * inverseProd ud

/-- Erdős Problem #1101, Question 1 (OPEN) [Er81h, p.178]:

Is there a good sequence u such that u(n) < n^{O(1)}?

Erdős believed the answer is NO: there is no good sequence with
polynomial growth. That is, for every C > 0 and every good sequence,
u(n) > n^C for infinitely many n. (This is exactly the negation of
"∃ C, u(n) ≤ n^C for all sufficiently large n"; restricting to C > 0 loses
nothing since u(n) ≥ 2 > 1 = n^C at n = 1 rules out C ≤ 0 anyway, and the
polynomial-growth class is invariant under the 0- vs 1-indexing shift.)
Stated as a direct assertion of the believed direction per this corpus's
convention for open yes/no questions. -/
theorem erdos_1101_no_polynomial_good_seq :
    ∀ ud : GoodSeqData, IsGoodSeq ud →
      ∀ C : ℝ, 0 < C → ∃ᶠ (n : ℕ) in atTop, (n : ℝ) ^ C < (ud.u n : ℝ) :=
  sorry

/-- Erdős Problem #1101, Question 2 (OPEN) [Er81h, p.178]:

Is there a good sequence u such that u(n) ≤ e^{o(n)}?

Erdős believed the answer is YES. That is, there exists a good sequence
such that log(u(n))/n → 0. (Equivalent to the source form: u(n) ≤ e^{f(n)}
with f(n)/n → 0 squeezes log(u(n))/n → 0 since log u(n) ≥ log 2 > 0, and
conversely f = log ∘ u works.) Stated as a direct assertion of the believed
direction per this corpus's convention for open yes/no questions. -/
theorem erdos_1101_subexponential_good_seq :
    ∃ ud : GoodSeqData, IsGoodSeq ud ∧
      Tendsto (fun n => Real.log (ud.u n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  sorry

/-- Erdős Problem #1101, existence of a good sequence (SOLVED) [Er81h, p.178]:

Erdős proved the existence of some good sequence; in his construction all the
u_i are primes. (The primality of the terms is recorded here in prose rather
than formalized, to avoid pulling in a primality import not otherwise used by
this file.) This also shows `erdos_1101_no_polynomial_good_seq` is not
vacuously quantified.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_1101.variants.exists_good_seq :
    ∃ ud : GoodSeqData, IsGoodSeq ud :=
  sorry

/-- Erdős Problem #1101, sieve lower bound (SOLVED, remark on the page):

An easy sieve argument proves that we always have, for any sequence u with
those properties,
max_{a_k<x} (a_{k+1} - a_k) > (1 + o(1)) t_x ∏(1 - 1/u_i)⁻¹.
Unpacked in the standard way: for every ε > 0 and all sufficiently large x,
the max gap exceeds (1 - ε) t_x ∏(1 - 1/u_i)⁻¹. So the bound in the
definition of "good" is best possible up to the factor (1 + ε).

(Stated with the windowed `maxGap` of this file; the CRT gap construction can
be placed with both endpoints ≤ x at the cost of one step down in t_x, which
the (1 - ε) form absorbs since t_x → ∞.)

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_1101.variants.sieve_lower_bound :
    ∀ ud : GoodSeqData, ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
      (1 - ε) * (tOfX ud x : ℝ) * inverseProd ud < (maxGap ud x : ℝ) :=
  sorry

end Erdos1101
