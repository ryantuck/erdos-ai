import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.LiminfLimsup

open Finset BigOperators Filter MeasureTheory

noncomputable section

namespace Erdos1132

/-!
# Erdős Problem #1132

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Let x₁, x₂, ... ∈ [-1,1] be an infinite sequence, and let
  L_n(x) = ∑_{1 ≤ k ≤ n} |l_k(x)|,
where each l_k(x) is defined with respect to x₁, ..., xₙ.

**Part 1:** Must there exist x ∈ (-1,1) such that
  L_n(x) > (2/π) log n - O(1)
for infinitely many n?

**Part 2:** Is it true that
  limsup_{n → ∞} L_n(x) / log n ≥ 2/π
for almost all x ∈ (-1,1)?

Status on erdosproblems.com/1132: OPEN ("This is open, and cannot be
resolved with a finite computation.") — page edition 23 January 2026,
accessed 2026-02-23. Source citations on the page: [Er67, p.68] and
[Va99, 2.43]. Tags: analysis | polynomials. No OEIS entry.

Remarks from the page: a result of Bernstein [Be31] *implies* that the set
of x ∈ (-1,1) for which
  limsup_{n → ∞} L_n(x) / log n ≥ 2/π
is everywhere dense (the page attributes the density statement as a
consequence of [Be31], not as its literal content). Erdős [Er61c] proved
that, for any fixed x₁, ..., xₙ ∈ [-1,1],
  max_{x ∈ [-1,1]} ∑_{1 ≤ k ≤ n} |l_k(x)| > (2/π) log n - O(1).
See also problem [1129] (`conjectures/1129.lean` in this repo) for more on
L_n(x), and also [1153] (`conjectures/1153.lean`).

References ([Be31]/[Er61c] recovered from the original pipeline's fetch of
erdosproblems.com/latex/1132 preserved in the session logs; that capture
contained no [Er67]/[Va99] entries, whose data is carried over from sibling
files sharing the keys (`conjectures-v2/1129.lean`,
`conjectures-v2/1130.lean`, `deepmind/deepmind/1153.lean`); volume numbers
were absent from all recovered extractions and are deliberately not
invented):

- [Er67] Erdős, P., _Problems and results on the convergence and divergence
  properties of the Lagrange interpolation polynomials and some extremal
  problems_. Mathematica (Cluj) (1967), 65–73. This problem: p. 68.
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §2.43.
- [Be31] Bernstein, S., _Sur la limitation des valeurs d'un polynome
  P_n(x) de degré n sur tout un segment par ses valeurs en (n+1) points du
  segment_. Izv. Akad. Nauk. SSSR (1931), 1025–1050.
- [Er61c] Erdős, P., _Problems and results on the theory of
  interpolation. II_. Acta Math. Acad. Sci. Hungar. (1961), 235–244.

NOTE: the Part 2 statement below was corrected by the Fable review of
2026-08-14 — the input file's ℝ-valued `Filter.limsup` encoding is provably
false as stated (see the docstring of `erdos_problem_1132_part2`) — and the
two variants were added from the recovered source page. None of these
changes are compile-verified (the review container cannot run `lake build`).
-/

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i)

    (This is the factorwise quotient; it agrees with the source's quotient
    of products whenever the nodes are pairwise distinct. For non-injective
    `nodes` a zero denominator makes the corresponding factor 0 by Lean's
    division convention; all uses below are guarded by the injectivity in
    `ValidSeq` or by an explicit injectivity hypothesis.) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: L_n(x) = ∑_k |lagrangeBasis nodes k x|.
    Degenerate cases: the empty sum gives L ≡ 0 for n = 0, and the empty
    product gives L ≡ 1 for n = 1; both are harmless under the `atTop`
    filters below. -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The first n elements of an infinite sequence, viewed as Fin n → ℝ.
    (Lean index i ∈ {0, …, n-1} corresponds to the source's 1-indexed
    x_{i+1}, so `firstN seq n` is exactly the source's x₁, …, xₙ.) -/
def firstN (seq : ℕ → ℝ) (n : ℕ) : Fin n → ℝ := fun i => seq i.val

/-- L_n(x): the Lebesgue function using the first n points of the sequence. -/
def L (seq : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  lebesgueFunction (firstN seq n) x

/-- A sequence is valid for interpolation: values in [-1,1] and pairwise
    distinct (`Function.Injective` — deliberately not `StrictMono`, since
    the problem adds the points in a prescribed order and the n-th Lebesgue
    function depends on which points come first, so arbitrary enumeration
    order must be allowed). -/
def ValidSeq (seq : ℕ → ℝ) : Prop :=
  Function.Injective seq ∧ ∀ i, seq i ∈ Set.Icc (-1 : ℝ) 1

/--
Erdős Problem #1132 (Part 1), OPEN:

For any infinite sequence x₁, x₂, ... ∈ [-1,1] of distinct points, must
there exist x ∈ (-1,1) and a constant C such that L_n(x) > (2/π) log n - C
for infinitely many n?

Equivalently: is limsup_{n} (L_n(x) - (2/π) log n) > -∞ for some
x ∈ (-1,1)? Stated as the raw-style direct assertion of the conjectured
affirmative, per this corpus's convention for open questions; the styled
form is `answer(sorry) ↔ ∀ seq, …` (cf. `deepmind/deepmind/1132.lean`).
The quantifier order ∃ x, ∃ C lets the O(1) constant depend on the point x,
which is the intended reading.
-/
theorem erdos_problem_1132_part1 (seq : ℕ → ℝ) (hseq : ValidSeq seq) :
    ∃ x ∈ Set.Ioo (-1 : ℝ) 1, ∃ C : ℝ,
      ∃ᶠ n in atTop,
        L seq n x > (2 / Real.pi) * Real.log (n : ℝ) - C :=
  sorry

/--
Erdős Problem #1132 (Part 2), OPEN — corrected encoding:

For any infinite sequence x₁, x₂, ... ∈ [-1,1] of distinct points, is it
true that limsup_{n → ∞} L_n(x) / log n ≥ 2/π for almost all x ∈ (-1,1)?

The limsup must be read in the extended sense (limsup = +∞ satisfies the
condition). It is encoded here as
  ∀ c < 2/π, L_n(x)/log n ≥ c for infinitely many n,
which is exactly equivalent to "limsup ≥ 2/π" valued in [-∞, +∞], with no
junk values. Stated as the raw-style direct assertion of the conjectured
affirmative; the styled form is `answer(sorry) ↔ ∀ seq, …`
(cf. `deepmind/deepmind/1132.lean`, which uses this same encoding).

Why the input file's encoding
  `Filter.limsup (fun n => L seq n x / Real.log n) atTop ≥ 2 / Real.pi`
was a defect: Mathlib's ℝ-valued `Filter.limsup` is
`sInf {a | ∀ᶠ n in atTop, f n ≤ a}`, and when f is not eventually bounded
above this set is empty, so `Real.sInf ∅ = 0` makes the Lean limsup 0 and
the inequality 0 ≥ 2/π false — precisely at points where the mathematical
limsup is +∞ and the intended condition holds trivially. This is not a
corner case: for the valid sequence x_k = 1/(k+1) (Lean: seq k = 1/(k+2))
and any x ∈ (-1,1) outside the countable set {0} ∪ {x_k}, one has
δ(x) := inf_k |x - x_k| > 0 while
∏_{i<n} |x_n - x_i| = 1/(n(n+1)^{n-1}) exactly, so
|l_n(x)| ≥ δ(x)^{n-1} · n(n+1)^{n-1} = n(δ(x)(n+1))^{n-1} → ∞
superexponentially; hence L_n(x)/log n → ∞ for a.e. x and the input file's
statement is provably FALSE for that sequence, independently of the open
conjecture.
-/
theorem erdos_problem_1132_part2 (seq : ℕ → ℝ) (hseq : ValidSeq seq) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)),
      ∀ c < 2 / Real.pi,
        ∃ᶠ n in atTop, L seq n x / Real.log (n : ℝ) ≥ c :=
  sorry

/--
Variant (page remark, SOLVED): a result of Bernstein [Be31] implies that,
for any infinite sequence x₁, x₂, ... ∈ [-1,1] of distinct points, the set
of x ∈ (-1,1) satisfying the (extended-sense) limsup condition
  limsup_{n → ∞} L_n(x) / log n ≥ 2/π
is everywhere dense in (-1,1). Density is encoded in the elementary
ε-formulation (every point of (-1,1) has such points arbitrarily close),
and the limsup condition uses the junk-free encoding of
`erdos_problem_1132_part2`.

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1132.variants.bernstein_dense (seq : ℕ → ℝ)
    (hseq : ValidSeq seq) :
    ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ∀ ε > 0, ∃ x ∈ Set.Ioo (-1 : ℝ) 1,
      |x - y| < ε ∧
      ∀ c < 2 / Real.pi, ∃ᶠ n in atTop, L seq n x / Real.log (n : ℝ) ≥ c :=
  sorry

/--
Variant (page remark, SOLVED by Erdős [Er61c]): for any fixed distinct
x₁, ..., xₙ ∈ [-1,1],
  max_{x ∈ [-1,1]} ∑_{1 ≤ k ≤ n} |l_k(x)| > (2/π) log n - O(1).

The O(1) is uniform: a single constant C works for every n and every choice
of nodes. The max over the compact interval is encoded by an existential
witness x ∈ [-1,1], which is exact (the maximum exceeds the bound iff some
point does). No small-n guard is needed: at n = 0 the sum is 0 and
`Real.log 0 = 0`, so the claim reads 0 > -C, and at n = 1 it reads 1 > -C;
any valid C is forced to be positive by the n = 0 case, and both cases then
hold.

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1132.variants.erdos_max_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (nodes : Fin n → ℝ),
      Function.Injective nodes → (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) →
      ∃ x ∈ Set.Icc (-1 : ℝ) 1,
        lebesgueFunction nodes x > (2 / Real.pi) * Real.log (n : ℝ) - C :=
  sorry

end Erdos1132
