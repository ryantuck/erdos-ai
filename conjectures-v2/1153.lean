import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Finset BigOperators

noncomputable section

namespace Erdos1153

/-!
# Erdős Problem #1153

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Let λ(x) = ∑_k |l_k(x)| (the Lebesgue function).

Is it true that, for any fixed -1 ≤ a < b ≤ 1,
  max_{x ∈ [a,b]} λ(x) > (2/π - o(1)) log n?

Verbatim source statement (erdosproblems.com/1153): "For
$x_1,\ldots,x_n\in [-1,1]$ let
\[l_k(x)=\frac{\prod_{i\neq k}(x-x_i)}{\prod_{i\neq k}(x_k-x_i)},\]
which are such that $l_k(x_k)=1$ and $l_k(x_i)=0$ for $i\neq k$. Let
\[\lambda(x)=\sum_k \lvert l_k(x)\rvert.\] Is it true that, for any fixed
$-1\leq a< b\leq 1$,
\[\max_{x\in [a,b]}\lambda(x)> \left(\frac{2}{\pi}-o(1)\right)\log n?\]"

Status on erdosproblems.com/1153: OPEN ("This is open, and cannot be
resolved with a finite computation.") — page edition 01 February 2026,
accessed 2026-02-23. Source line: #1153: [Va99, 2.44]. Tags: analysis |
polynomials. Formalised statement (per the page, as of access): No.
Additional thanks to: Wouter van Doorn. (An intermediate pipeline
extraction and the archived styled copy `deepmind/deepmind/1153.lean`
recorded this problem as PROVED/`research solved` with `answer(True)`;
that status is a WebFetch-summarizer hallucination contradicted by the
archived page HTML, whose banner, tooltip, and open-status disclaimer all
say OPEN. See fable-review/1153.md.)

Remarks from the page: Bernstein [Be31] proved this for a = -1 and b = 1,
and Erdős [Er61c] improved this to
  max_{x ∈ [-1,1]} λ(x) > (2/π) log n - O(1).
This is best possible, since taking the xᵢ as the roots of the nth
Chebyshev polynomial yields max_{x ∈ [-1,1]} λ(x) < (2/π) log n + O(1).
See also problems [1129] (`conjectures/1129.lean` in this repo) and
[1132] (`conjectures/1132.lean`).

The conjecture asks whether the same lower bound (up to o(1) in the
coefficient) holds when the maximum is restricted to any subinterval
[a,b] ⊆ [-1,1].

Encoding notes:

* The source poses a yes/no question and the problem is OPEN; this raw
  corpus has no `answer()` elaborator (Mathlib-only imports), and its
  uniform convention for open yes/no questions is a direct assertion of
  the asked ("yes") direction with a `sorry` proof, as here. In styled
  question form it would be `answer(sorry) ↔ ∀ a b : ℝ, …` (the archived
  styled copy instead used `answer(True)`, which asserts the question is
  *known* to have answer yes — wrong for an OPEN problem).
* The o(1) is encoded as: for every ε > 0 there is N (depending on a, b,
  ε only) beyond which the bound (2/π - ε) log n holds for **all** node
  configurations. This uniform reading is equivalent to the
  per-configuration reading by a diagonalization argument, so no content
  hangs on the choice.
* `max_{x ∈ [a,b]} λ(x) > c` is encoded as `∃ x ∈ Set.Icc a b,
  lebesgueFunction nodes x > c`, which is exactly equivalent (for the
  strict inequality the sup exceeds c iff some point does; no `sSup`
  machinery is needed).
* Small n are harmless: the prover picks N, and for n = 0 (λ ≡ 0,
  `Real.log 0 = 0`) the conclusion fails, so any proof must take N ≥ 1;
  for n = 1, λ ≡ 1 and log 1 = 0 make the bound trivial.

References ([Be31]/[Er61c] recovered from the original pipeline's fetch of
erdosproblems.com/latex/1153 preserved in the session logs; [Va99] is the
corpus-canonical identity of this site-global key, carried from sibling
files; volume numbers were absent from all recovered extractions and are
deliberately not invented):

- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §2.44.
- [Be31] Bernstein, S., _Sur la limitation des valeurs d'un polynome
  P_n(x) de degré n sur tout un segment par ses valeurs en (n+1) points du
  segment_. Izv. Akad. Nauk. SSSR (1931), 1025–1050.
- [Er61c] Erdős, P., _Problems and results on the theory of
  interpolation. II_. Acta Math. Acad. Sci. Hungar. (1961), 235–244.

NOTE: the module-docstring enrichment, the definition-docstring notes, and
the three variants below are from the Fable review of 2026-08-14 and are
**not compile-verified** (the review container cannot run `lake build`).
The main theorem statement is unchanged from `conjectures/1153.lean`,
which compiled successfully in its originating session.
-/

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i)

    (This is the factorwise quotient; it agrees with the source's quotient
    of products whenever the nodes are pairwise distinct. For non-injective
    `nodes` a zero denominator makes the corresponding factor 0 by Lean's
    division convention; all uses below are guarded by the injectivity in
    `ValidNodes`.) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: λ(x) = ∑_k |l_k(x)|.
    Degenerate cases: the empty sum gives λ ≡ 0 for n = 0, and the empty
    product gives λ ≡ 1 for n = 1; both are harmless under the ∃N
    threshold in the statements below. For n ≥ 1 and distinct nodes,
    λ(x) ≥ 1 everywhere, since ∑_k l_k(x) = 1 (Lagrange interpolation of
    the constant 1). -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- Nodes are valid: pairwise distinct and in [-1, 1]. (`Function.Injective`
    rather than `StrictMono`: the Lebesgue function is invariant under
    permutations of the nodes, so the enumeration order is immaterial
    here.) -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/--
Erdős Problem #1153 [Va99, 2.44] (OPEN):

For any fixed -1 ≤ a < b ≤ 1 and any ε > 0, there exists N such that for all
n ≥ N, for any choice of n distinct nodes x₁, ..., xₙ ∈ [-1,1],
  max_{x ∈ [a,b]} ∑_k |l_k(x)| > (2/π - ε) · log n.

This theorem asserts the "yes" direction of the open question, per this
corpus's convention for open yes/no questions (in styled question form it
would be `answer(sorry) ↔ ∀ a b : ℝ, …`). Bernstein [Be31] proved the case
a = -1, b = 1 (see `erdos_problem_1153.variants.bernstein`); the general
subinterval case is open.
-/
theorem erdos_problem_1153 (a b : ℝ) (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ nodes : Fin n → ℝ, ValidNodes nodes →
        ∃ x ∈ Set.Icc a b,
          lebesgueFunction nodes x > (2 / Real.pi - ε) * Real.log (n : ℝ) :=
  sorry

/--
Variant (page remark, SOLVED by Bernstein [Be31]): the case a = -1, b = 1
of the problem — for any ε > 0 and all sufficiently large n, every choice
of n distinct nodes in [-1,1] has
  max_{x ∈ [-1,1]} ∑_k |l_k(x)| > (2/π - ε) · log n.

This is the instance a = -1, b = 1 of `erdos_problem_1153`, stated
separately because it is a theorem while the general subinterval case is
open. (Erdős's sharper form with an additive O(1) error is
`erdos_problem_1153.variants.erdos_full_interval`.)

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1153.variants.bernstein (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ nodes : Fin n → ℝ, ValidNodes nodes →
        ∃ x ∈ Set.Icc (-1 : ℝ) 1,
          lebesgueFunction nodes x > (2 / Real.pi - ε) * Real.log (n : ℝ) :=
  sorry

/--
Variant (page remark, SOLVED by Erdős [Er61c]): for any fixed distinct
x₁, ..., xₙ ∈ [-1,1],
  max_{x ∈ [-1,1]} ∑_k |l_k(x)| > (2/π) log n - O(1).

The O(1) is uniform: a single constant C works for every n and every choice
of nodes. The max over the compact interval is encoded by an existential
witness x ∈ [-1,1], which is exact (the maximum exceeds the bound iff some
point does). No small-n guard is needed: at n = 0 the sum is 0 and
`Real.log 0 = 0`, so the claim reads 0 > -C, and at n = 1 it reads 1 > -C;
any valid C is forced to be positive by the n = 0 case, and both cases then
hold. (This statement also appears, identically encoded, as
`erdos_problem_1132.variants.erdos_max_bound` in `conjectures-v2/1132.lean`,
whose source page carries the same remark.)

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1153.variants.erdos_full_interval :
    ∃ C : ℝ, ∀ (n : ℕ) (nodes : Fin n → ℝ),
      ValidNodes nodes →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        lebesgueFunction nodes x > (2 / Real.pi) * Real.log (n : ℝ) - C :=
  sorry

/--
Variant (page remark, SOLVED): the lower bound of [Er61c] is best possible —
there is a constant C such that for every n some choice of n distinct nodes
in [-1,1] (namely the roots cos((2k+1)π/(2n)), k = 0, ..., n-1, of the nth
Chebyshev polynomial) satisfies
  max_{x ∈ [-1,1]} ∑_k |l_k(x)| < (2/π) log n + C.

The witness is stated existentially (the specific Chebyshev configuration
is recorded here in prose only, keeping the statement to constructs already
in this file); the universal ∀ x ∈ [-1,1] bound is the "max < RHS" reading.
No small-n guard is needed: n = 0 (empty nodes, λ ≡ 0) and n = 1 (λ ≡ 1,
log 1 = 0) hold as soon as C > 1, and the asymptotic result absorbs the
remaining finitely many n into C.

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1153.variants.chebyshev_best_possible :
    ∃ C : ℝ, ∀ n : ℕ, ∃ nodes : Fin n → ℝ, ValidNodes nodes ∧
      ∀ x ∈ Set.Icc (-1 : ℝ) 1,
        lebesgueFunction nodes x < (2 / Real.pi) * Real.log (n : ℝ) + C :=
  sorry

end Erdos1153
