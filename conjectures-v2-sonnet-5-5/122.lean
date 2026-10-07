-- [AI - Claude Sonnet 5.5]: Erdős Problem 122 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecificLimits.Basic

open Classical Filter Finset

/-!
# Erdős Problem #122: Locally Repeated Values of $n + f(n)$

*Source:* [erdosproblems.com/122](https://www.erdosproblems.com/122) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-20 as the tidied
problem box). [Er97] [Er97e] [EPS97]

For which number theoretic functions $f$ is it true that, for any $F(n)$ such that
$f(n)/F(n)\to 0$ for almost all $n$, there are infinitely many $x$ such that
$$\frac{\#\{ n\in \mathbb{N} : n+f(n)\in (x,x+F(x))\}}{F(x)}\to \infty?$$

Remarks recorded on the page:
* Asked by Erdős, Pomerance, and Sárközy [EPS97] who prove that this is true when $f$ is the
  divisor function or the number of distinct prime divisors of $n$, but Erdős believed it is
  false when $f(n)=\phi(n)$ or $\sigma(n)$.

Tags: number theory.

**The literal statement is degenerate.** Every $n$ with $n+f(n)\in(x,x+F(x))$ has
$n<x+F(x)$, so the count is below $x+F(x)$ and the ratio is at most $1+x/F(x)$. If $F(x)\ge
x+1$ the ratio is at most $3$. Now take, for any $f$,
$$F(n)=(n+1)(f(n)+1).$$
Then $F(n)\ge n+1$, and $f(n)/F(n)\le 1/(n+1)\to 0$ for every $n$. So no function $f$ has the
property as literally stated, and the answer to "for which $f$?" would be "none". That
contradicts the page's own remark that the property is a theorem for the divisor functions. So
the page leaves a restriction on the size of $F$ unstated; the cited theorem [EPS97] must be about
small $F$. The same count shows how small. For the divisor function $\tau$ and $F(x)=\sqrt x$,
the ratio tends to $1$, because $\tau(n)\le n^{o(1)}$ and so at most $x^{o(1)}$ values of
$n\le x$ land above $x$. Numerically, for $x=10^5$ the ratio is $1.002$. So a theorem for the
divisor functions can only concern $F$ with $F(x)\le x^{o(1)}$ at the relevant $x$. That is an
inference from the count, not something recovered from the source.

**What this file does.**
* The first pass's four definitions are unchanged. They are the literal reading.
* `erdos_problem_122` is now the true statement of that reading: no $f$ has the property.
  It is proved here, with no `sorry`.
* The first pass's theorem, that $\tau$ and $\omega$ have the property, is false. It appears as
  `variants.first_pass_false`, and is a corollary.
* The intended restricted property is **DEFERRED**. It needs the exact hypothesis on $F$ from
  [EPS97] or [Er97e], neither of which could be read in this review. No guess is formalized.

**Encoding notes.**
* `x : ℕ` and `F : ℕ → ℝ`. The degeneracy does not depend on that choice.
* "$f(n)/F(n)\to0$ for almost all $n$" is: for every $\varepsilon>0$ the set
  $\{n : f(n)/F(n)\ge\varepsilon\}$ has natural density $0$. "$\to\infty$ for infinitely many
  $x$" is: for every $C$, infinitely many $x$ have ratio $>C$.
* `shiftCount` searches $n\in[0,x+\lceil F(x)\rceil]$, which suffices because
  $n\le n+f(n)<x+F(x)$. At $n=0$ the divisor functions give $0+0=0\notin(x,\cdot)$, so $n=0$
  never counts for them.

## References

* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.
* [EPS97] Erdős, P., Pomerance, C. and Sárközy, A., _On locally repeated values of certain
  arithmetic functions. IV_. Ramanujan J. (1997), 227–241.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/122` gives only [EPS97],
with its title, journal and pages. [Er97] and [Er97e] are from the bibliographies of upstream
`formal-conjectures` files for sibling problems, for example `121.lean`. Citation keys are shared
across the site. [Er97e]'s title also appears in sibling `/latex` extractions. No `/latex`
extraction recovered from the logs gives [Er97].)
-/

/-- The count of natural numbers n such that n + f(n) falls in the open real
    interval (x, x + F(x)). Since n ≤ n + f(n) < x + F(x) requires n < x + F(x),
    it suffices to search n in the range [0, x + ⌈F x⌉₊]. -/
noncomputable def shiftCount (f : ℕ → ℕ) (F : ℕ → ℝ) (x : ℕ) : ℕ :=
  ((Finset.range (x + ⌈F x⌉₊ + 1)).filter
    (fun (n : ℕ) => (x : ℝ) < (n : ℝ) + (f n : ℝ) ∧
              (n : ℝ) + (f n : ℝ) < (x : ℝ) + F x)).card

/-- The natural density of a set A ⊆ ℕ is zero: the proportion of elements
    in {0, …, N−1} belonging to A tends to 0 as N → ∞. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop (nhds 0)

/-- f(n)/F(n) → 0 for almost all n in the natural-density sense:
    for every ε > 0, the set {n : f(n)/F(n) ≥ ε} has natural density zero. -/
def AlmostAllRatioVanishes (f : ℕ → ℕ) (F : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → HasNaturalDensityZero {n : ℕ | ε ≤ (f n : ℝ) / F n}

/-- The Erdős–122 property of f: for any positive F with f(n)/F(n) → 0
    in natural density, the ratio #{n ∈ ℕ : n+f(n) ∈ (x, x+F(x))} / F(x)
    is unbounded as x → ∞ (equivalently, its limsup equals +∞). -/
def HasErdos122Property (f : ℕ → ℕ) : Prop :=
  ∀ F : ℕ → ℝ, (∀ n, 0 < F n) → AlmostAllRatioVanishes f F →
    ∀ C : ℝ, ∃ᶠ x : ℕ in atTop, C < (shiftCount f F x : ℝ) / F x

/--
Erdős Problem #122 [Er97, Er97e, EPS97] — OPEN as intended; DEGENERATE as literally stated.

For which number-theoretic functions f : ℕ → ℕ is it true that for any positive function
F : ℕ → ℝ satisfying f(n)/F(n) → 0 for almost all n (in the natural density sense), there are
infinitely many x for which

  #{n ∈ ℕ : n + f(n) ∈ (x, x + F(x))} / F(x) → ∞?

Read literally, as `HasErdos122Property`, the answer is: for no f. Take F(n) = (n+1)(f(n)+1).
Then f(n)/F(n) ≤ 1/(n+1) for every n, so the density hypothesis holds. And F(x) ≥ x + 1, while
the count is at most x + ⌈F x⌉ + 1, so the ratio never exceeds 3.

This contradicts the page's remark that [EPS97] proved the property for the divisor function and
for ω. So the page leaves an upper bound on F unstated. The intended property is not formalized.
-/
theorem erdos_problem_122 : ∀ f : ℕ → ℕ, ¬ HasErdos122Property f := by
  intro f h
  -- the adversarial F
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ → ℝ, ∀ n, F n = ((n : ℝ) + 1) * ((f n : ℝ) + 1) :=
    ⟨fun n => ((n : ℝ) + 1) * ((f n : ℝ) + 1), fun _ => rfl⟩
  have hf0 : ∀ n, (0 : ℝ) ≤ (f n : ℝ) := fun n => Nat.cast_nonneg _
  have hn0 : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) := fun n => Nat.cast_nonneg _
  have hFpos : ∀ n, 0 < F n := fun n => by
    rw [hFdef]
    have := hf0 n
    have := hn0 n
    positivity
  have hFge : ∀ n : ℕ, (n : ℝ) + 1 ≤ F n := fun n => by
    rw [hFdef]
    nlinarith [hf0 n, hn0 n]
  -- a finite set has natural density zero
  have key : ∀ A : Set ℕ, A.Finite → HasNaturalDensityZero A := by
    intro A hA
    unfold HasNaturalDensityZero
    have hK : ∀ N : ℕ, (((Finset.range N).filter (· ∈ A)).card : ℝ) ≤ (hA.toFinset.card : ℝ) := by
      intro N
      exact_mod_cast Finset.card_le_card
        (fun n hn => hA.mem_toFinset.mpr (Finset.mem_filter.mp hn).2)
    exact squeeze_zero (fun N => by positivity)
      (fun N => by have := hK N; gcongr)
      (tendsto_const_div_atTop_nhds_zero_nat _)
  -- the density hypothesis holds: each exceptional set is finite
  have hdens : AlmostAllRatioVanishes f F := by
    intro ε hε
    apply key
    refine (Finset.range ⌈1 / ε⌉₊).finite_toSet.subset ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by have := hn0 n; positivity
    have hle : (f n : ℝ) / F n ≤ 1 / ((n : ℝ) + 1) := by
      rw [div_le_div_iff₀ (hFpos n) hn1, hFdef]
      nlinarith [hf0 n, hn0 n]
    have h2 : ε ≤ 1 / ((n : ℝ) + 1) := hn.trans hle
    rw [le_div_iff₀ hn1] at h2
    rw [Nat.lt_ceil, lt_div_iff₀ hε]
    nlinarith
  -- the count is at most the length of the search range, so the ratio is at most 3
  have hbound : ∀ x : ℕ, (shiftCount f F x : ℝ) / F x ≤ 3 := by
    intro x
    rw [div_le_iff₀ (hFpos x)]
    have h1 : (shiftCount f F x : ℝ) ≤ (x : ℝ) + (⌈F x⌉₊ : ℝ) + 1 := by
      have : shiftCount f F x ≤ x + ⌈F x⌉₊ + 1 := by
        unfold shiftCount
        exact (Finset.card_filter_le _ _).trans (Finset.card_range _).le
      exact_mod_cast this
    have h2 : (⌈F x⌉₊ : ℝ) < F x + 1 := Nat.ceil_lt_add_one (hFpos x).le
    have h3 := hFge x
    have h4 := hn0 x
    linarith
  obtain ⟨x, hx⟩ := (h F hFpos hdens 3).exists
  exact absurd (hbound x) (not_le.mpr hx)

/--
The first-pass theorem is false: the divisor function τ and the function ω do not have the
property `HasErdos122Property`, as literally defined. (A corollary of `erdos_problem_122`.)
-/
theorem erdos_problem_122.variants.first_pass_false :
    ¬ (HasErdos122Property (fun n => (Nat.divisors n).card) ∧
       HasErdos122Property (fun n => (Nat.primeFactorsList n).toFinset.card)) :=
  fun h => erdos_problem_122 _ h.1

/--
Under the literal reading, Erdős's belief for φ holds trivially: Euler's totient function does not
have the property. This is a theorem there, not an open belief. (A corollary of
`erdos_problem_122`.)
-/
theorem erdos_problem_122.variants.not_totient : ¬ HasErdos122Property Nat.totient :=
  erdos_problem_122 _

/--
Under the literal reading, Erdős's belief for σ holds trivially too: the sum-of-divisors function
does not have the property. (A corollary of `erdos_problem_122`.)
-/
theorem erdos_problem_122.variants.not_sigma :
    ¬ HasErdos122Property (fun n => ∑ d ∈ Nat.divisors n, d) :=
  erdos_problem_122 _
