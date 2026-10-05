-- [AI - Claude Sonnet 5.5]: Erdős Problem 124 — second-pass formalization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators
open Finset Filter

/-!
# Erdős Problem #124: Sums of Elements of Digit-Restricted Power Sets

*Source:* [erdosproblems.com/124](https://www.erdosproblems.com/124) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-20 and 2026-03-05
as the tidied problem box). [BEGL96] [Er97, p.156] [Er97e, p.533]

For any $d\geq 1$ and $k\geq 0$ let $P(d,k)$ be the set of integers which are the sum of
distinct powers $d^i$ with $i\geq k$. Let $3\leq d_1<d_2<\cdots <d_r$ be integers such that
$$\sum_{1\leq i\leq r}\frac{1}{d_i-1}\geq 1.$$
Can all sufficiently large integers be written as a sum of the shape $\sum_i c_ia_i$ where
$c_i\in \{0,1\}$ and $a_i\in P(d_i,0)$?

If we further have $\gcd(d_1,\ldots,d_r)=1$ then, for any $k\geq 1$, can all sufficiently large
integers be written as a sum of the shape $\sum_i c_ia_i$ where $c_i\in \{0,1\}$ and
$a_i\in P(d_i,k)$?

(The page prints the summand as $1/(d_r-1)$. The index must be $i$.)

Remarks recorded on the page:
* The second question was conjectured by Burr, Erdős, Graham, and Li [BEGL96], who proved it
  for $\{3,4,7\}$.
* The first question was asked separately by Erdős in [Er97] and [Er97e], although there is
  some ambiguity over whether he intended $P(d,0)$ or $P(d,1)$. Certainly he mentions no gcd
  condition. A simple positive proof of the first question was provided (and formalised in
  Lean) by Aristotle thanks to Alexeev; see the comments for details.
* In [BEGL96] they record that Pomerance observed that the condition $\sum 1/(d_i-1)\geq 1$ is
  necessary (for both questions), but give no details. Tao has sketched an explanation in the
  comments. It is trivial that $\gcd(d_1,\ldots,d_r)=1$ is a necessary condition in the second
  question.
* Melfi [Me04] gives a construction, for any $\epsilon>0$, of an infinite set of $d_i$ for which
  every sufficiently large integer can be written as a finite sum of the shape $\sum_i c_ia_i$
  where $c_i\in \{0,1\}$ and $a_i\in P(d_i,0)$ and yet $\sum_{i}\frac{1}{d_i-1}<\epsilon$.
* See also Problem #125.

Tags: number theory, base representations, complete sequences.

**Status of the two parts.** The first question is answered **yes**, by the page's own remarks.
Upstream `erdos124.zero` is `answer(True)`, credited to Alexeev using Aristotle. The second
question is OPEN: the mirror has `open`, and upstream has `answer(sorry)`. The banner reads OPEN
because of the second question. The first pass labelled the first question OPEN too, although its
docstring notes the proof. This second-pass review has not checked the proof, and the page's 13
comments were not captured.

**Encoding.**
* Both parts quantify over a `Finset` of integers $\ge3$ (strictly increasing is automatic).
* The coefficients $c_i\in\{0,1\}$ are absorbed: $0\in P(d,k)$ (the empty sum), so choosing
  $c_i=0$ is choosing $a_i=0$. A representation is `N = ∑ d ∈ ds, f d` with
  `f d ∈ powerSumSet d k`.
* `powerSumSet d k` is $P(d,k)$. For $d\ge3$ it is the set of integers whose base-$d$ digits are
  all $0$ or $1$ and vanish below position $k$.
* $d-1\ge2$, so no division by zero. The sum is taken in ℝ, after casting, so there is no ℕ
  subtraction.
* The hypothesis $\sum 1/(d-1)\ge1$ forces at least three elements. With
  $d\ge3$ the two largest terms are $1/2$ and $1/3$.
* **Melfi's result and $k=0$.** With infinitely many bases, $1=d_i^0\in P(d_i,0)$ lets any $n$
  be written as $n$ ones from $n$ distinct bases. So Melfi's statement as the page words it,
  with $P(d_i,0)$, is trivial. The non-trivial statement needs $k\ge1$. `variants.melfi`
  records that, following upstream.

## References

* [BEGL96] Burr, S. A., Erdős, P., Graham, R. L. and Li, W. W.-C., _Complete sequences of sets of
  integer powers_. Acta Arith. (1996), 133–138.
* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.
* [Me04] Melfi (2004), in the page's remarks. **DEFERRED:** no bibliographic details were
  recovered. Upstream cites "Melfi [Me04, Proposition 1]" without a bibliography entry.

(Provenance: no `/latex/124` fetch exists in the session logs. [BEGL96] is from upstream
`124.lean`; no other source for it was recovered. [Er97] and [Er97e] are from the bibliographies
of upstream `formal-conjectures` files for sibling problems, for example `121.lean`.)
-/

/-- P(d, k): the set of natural numbers expressible as a sum of distinct powers
    d^i with i ≥ k. These are the numbers whose base-d representation uses only
    digits 0 and 1 in positions ≥ k. -/
def powerSumSet (d : ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ i ∈ S, k ≤ i) ∧ n = ∑ i ∈ S, d ^ i}

/--
Erdős Problem #124, Part 1 [Er97, Er97e] — PROVED (a positive proof by Aristotle, thanks to
Alexeev, per the page's remarks; the page banner reads OPEN because Part 2 is open)

For any d ≥ 1 and k ≥ 0 let P(d,k) be the set of integers which are the sum of
distinct powers d^i with i ≥ k.

Let 3 ≤ d₁ < d₂ < ⋯ < d_r be integers such that ∑ 1/(dᵢ-1) ≥ 1. Can all
sufficiently large integers be written as a sum ∑ cᵢaᵢ where cᵢ ∈ {0,1} and
aᵢ ∈ P(dᵢ, 0)?

Note: since 0 ∈ P(d, k) (via the empty sum), choosing cᵢ = 0 is equivalent to
choosing aᵢ = 0, so the question is simply whether N = ∑_{d ∈ ds} f(d) with f(d) ∈ P(d, 0).

A positive proof was provided by Aristotle (thanks to Alexeev); see the website
comments for details.
-/
theorem erdos_problem_124a :
    ∀ ds : Finset ℕ, (∀ d ∈ ds, 3 ≤ d) →
    1 ≤ ∑ d ∈ ds, (1 : ℝ) / ((d : ℝ) - 1) →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d 0) ∧
        N = ∑ d ∈ ds, f d :=
  sorry

/--
Erdős Problem #124, Part 2 [BEGL96] — OPEN

Under the same hypotheses as Part 1, if additionally gcd(d₁, …, d_r) = 1, then
for any k ≥ 1, all sufficiently large integers can be written as ∑ cᵢaᵢ where
cᵢ ∈ {0,1} and aᵢ ∈ P(dᵢ, k).

This was conjectured by Burr, Erdős, Graham, and Li [BEGL96], who proved it for
{3, 4, 7}.
-/
theorem erdos_problem_124b :
    ∀ ds : Finset ℕ, (∀ d ∈ ds, 3 ≤ d) →
    1 ≤ ∑ d ∈ ds, (1 : ℝ) / ((d : ℝ) - 1) →
    ds.gcd id = 1 →
    ∀ k : ℕ, 1 ≤ k →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d k) ∧
        N = ∑ d ∈ ds, f d :=
  sorry

/--
Pomerance's observation, recorded in [BEGL96] (PROVED; the page gives no details and Tao sketched
an explanation in the comments): the condition ∑ 1/(dᵢ-1) ≥ 1 is necessary in Part 1. It is also
necessary in Part 2, since P(d, k) ⊆ P(d, 0).
-/
theorem erdos_problem_124.variants.pomerance
    (ds : Finset ℕ) (hds : ∀ d ∈ ds, 3 ≤ d) :
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d 0) ∧ N = ∑ d ∈ ds, f d) →
    1 ≤ ∑ d ∈ ds, (1 : ℝ) / ((d : ℝ) - 1) :=
  sorry

/--
The gcd condition is necessary in Part 2 (PROVED; trivial): for k ≥ 1 every element of P(d, k) is a
multiple of d, so if the gcd of the bases is not 1 then, for every N₀, some N ≥ N₀ is not a
multiple of the gcd and so is not representable.
-/
theorem erdos_problem_124.variants.gcd_necessary
    (ds : Finset ℕ) (hds : ∀ d ∈ ds, 3 ≤ d) (hg : ds.gcd id ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    ¬ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d k) ∧ N = ∑ d ∈ ds, f d :=
  sorry

/--
Burr, Erdős, Graham and Li [BEGL96] (PROVED): Part 2 holds for {3, 4, 7}. Here the case k = 1,
which is the case upstream records. Note ∑ 1/(d-1) = 1/2 + 1/3 + 1/6 = 1 exactly, so this is the
borderline of the necessary condition. The page does not say which k are covered.
-/
theorem erdos_problem_124.variants.begl_three_four_seven :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ({3, 4, 7} : Finset ℕ), f d ∈ powerSumSet d 1) ∧
        N = ∑ d ∈ ({3, 4, 7} : Finset ℕ), f d :=
  sorry

/--
Melfi [Me04] (PROVED): for every ε > 0 there is an infinite increasing sequence of bases dᵢ with
∑ 1/(dᵢ - 1) < ε such that, for every k ≥ 1, all large N are finite sums ∑_{i ∈ I} aᵢ with
aᵢ ∈ P(dᵢ, k). The page words this for P(dᵢ, 0), where it is trivial (see the module docstring);
this is the non-trivial form, as in upstream.
-/
theorem erdos_problem_124.variants.melfi :
    ∀ ε : ℝ, 0 < ε → ∃ d : ℕ → ℕ, StrictMono d ∧ 2 ≤ d 0 ∧
      Summable (fun i => 1 / ((d i : ℝ) - 1)) ∧ ∑' i, 1 / ((d i : ℝ) - 1) < ε ∧
      ∀ k : ℕ, 1 ≤ k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ (I : Finset ℕ) (a : ℕ → ℕ), (∀ i ∈ I, a i ∈ powerSumSet (d i) k) ∧
          N = ∑ i ∈ I, a i :=
  sorry
