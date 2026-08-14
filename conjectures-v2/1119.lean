import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Erdős Problem #1119

Source: https://www.erdosproblems.com/1119 (page last edited 31 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $\mathfrak{m}$ be an infinite cardinal with
$\aleph_0<\mathfrak{m}<\mathfrak{c}=2^{\aleph_0}$. Let $\{f_\alpha\}$ be a
family of entire functions such that, for every $z_0\in \mathbb{C}$, there are
at most $\mathfrak{m}$ distinct values of $f_\alpha(z_0)$. Must $\{f_\alpha\}$
have cardinality at most $\mathfrak{m}$?"

Status: INDEPENDENT (banner tooltip: "Independent of the usual axioms of set
theory (ZFC)."). Tags: analysis, set theory. Attribution: "This is Problem
2.46 in [Ha74], where it is attributed to Erdős."

Remarks from the page:

* Erdős [Er64g] proved (answering a question of Wetzel) that if there are only
  countably many distinct values for each $f_\alpha(z_0)$ then, if
  $\mathfrak{c}>\aleph_1$, the family $\{f_\alpha\}$ is itself countable, and
  also showed this is false if $\mathfrak{c}=\aleph_1$.
* In [Ha74] it is written that it is 'easy to see' the answer is yes if
  $\mathfrak{m}^+<\mathfrak{c}$, and also that it is possible that the
  question is undecidable.
* Indeed, it has been shown that this is undecidable if
  $\mathfrak{m}^+=\mathfrak{c}$: Kumar and Shelah [KuSh17] have shown that
  there is a model in which $\mathfrak{c}=\aleph_2$ such that the answer is
  yes (with $\mathfrak{m}=\aleph_1$), while Schilhan and Weinert [ScWe24]
  have shown the answer can be no, in a different model with
  $\mathfrak{c}=\aleph_2$.

Encoding notes:

* The problem is a yes/no question whose answer is INDEPENDENT of ZFC (for
  the critical case $\mathfrak{m}^+ = \mathfrak{c}$, hence for the universal
  statement over all admissible $\mathfrak{m}$: it holds in the Kumar–Shelah
  model and vacuously under CH, and fails in the Schilhan–Weinert model).
  This raw-file corpus has no `answer()` elaborator (a formal-conjectures
  construct), and the corpus convention for OPEN yes/no questions — a direct
  assertion of a definite direction — is unfaithful here: the first-pass file
  asserted the affirmative direction as a theorem, but that assertion is
  neither provable nor refutable (relative to the consistency of the relevant
  forcing extensions), so no direction can honestly be asserted. The
  question's content is therefore recorded as a `Prop`-valued definition
  (`ErdosProblem1119Statement`), and the ZFC-provable parts of the problem's
  resolution — the 'easy' case $\mathfrak{m}^+ < \mathfrak{c}$ from [Ha74]
  and both directions of Erdős's countable case [Er64g] — are formalized as
  theorems below. The two independence results themselves ([KuSh17],
  [ScWe24]) are consistency statements about models of ZFC and are not
  directly expressible as single Lean statements (same treatment as the
  ZFC-independent variant in problem #1067); they are recorded in prose only.
  NOTE: this restatement is not compile-verified (no `lake build` in the
  review container).
* Restricting the index type to `Type` (= `Type 0`) loses no generality: the
  hypotheses and conclusion depend only on `range f ⊆ ℂ → ℂ` (which lives in
  `Type 0`), and any family indexed by a higher universe induces the same
  value sets and the same set of distinct functions after re-indexing by
  `↥(range f)`.
* $\mathfrak{m}^+$ (the successor cardinal) is `Order.succ 𝔪`; on cardinals
  `Order.succ 𝔪` is the least cardinal exceeding `𝔪`, so
  `Order.succ 𝔪 < continuum` is equivalent to the existence of a cardinal
  strictly between `𝔪` and `𝔠`.
* "Only countably many distinct values" is `≤ ℵ₀` (finite value sets are
  allowed), and $\mathfrak{c} > \aleph_1$ / $\mathfrak{c} = \aleph_1$ (CH)
  are `aleph 1 < continuum` / `continuum = aleph 1`.

References (citation keys from the archived page; the page HTML loads
bibliographic details via separate `/bibs/` requests that are not in the
session logs, so the data below comes from sibling files and reviewer
knowledge as noted, and is NOT verified against
erdosproblems.com/latex/1119 — treat as honest stubs):

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180. (Bibliographic data as carried, in agreement, by the sibling
formalizations of this same key for problems 114, 225 (deepmind), 226, 229,
230, 1115–1118, 1120.)

[Er64g] Erdős, P., _An interpolation problem associated with the continuum
hypothesis_, Michigan Math. J. 11 (1964), 9–10. (Bibliographic data from the
archived styled formalization of this problem, consistent with reviewer
knowledge of the paper.)

[KuSh17] Kumar, A. and Shelah, S., _On a question about families of entire
functions_, Fund. Math. 239 (2017), 279–288. (First-pass pipeline capture and
the archived styled formalization agree on this entry.)

[ScWe24] Schilhan, J. and Weinert, T., _Wetzel families and the continuum_,
J. London Math. Soc. (2) (2024), e12918. (The first-pass pipeline recorded
this key as "On Wetzel's problem and its relatives, preprint (2024)"; the
archived styled formalization corrected it to the title above, which matches
reviewer knowledge of the paper (arXiv:2310.19473) and is used here.)

Formalised statement in external databases: No (as of the archived capture).
The page shows 1 forum comment and no related OEIS sequences or
cross-referenced problems. Additional thanks to: Jake Mallen.
-/

noncomputable section
open Cardinal Classical Set

namespace Erdos1119

/--
Erdős Problem #1119 (Problem 2.46 in [Ha74], attributed to Erdős; the answer
is INDEPENDENT of ZFC):

Let 𝔪 be an infinite cardinal with ℵ₀ < 𝔪 < 𝔠 = 2^{ℵ₀}. Let {f_α} be a family
of entire functions such that, for every z₀ ∈ ℂ, there are at most 𝔪 distinct
values of f_α(z₀). Must {f_α} have cardinality at most 𝔪?

This `Prop` is the affirmative answer to the question, for every admissible
𝔪 simultaneously. It is recorded as a definition rather than asserted as a
theorem because it is independent of ZFC: Kumar–Shelah [KuSh17] produced a
model (with 𝔠 = ℵ₂, 𝔪 = ℵ₁) in which the answer is yes — and under CH the
statement holds vacuously, there being no admissible 𝔪 — while
Schilhan–Weinert [ScWe24] produced a model (also with 𝔠 = ℵ₂) in which the
answer is no. Undecidability can only occur at 𝔪⁺ = 𝔠; see
`erdos_problem_1119.variants.easy_case` for the ZFC-provable case 𝔪⁺ < 𝔠,
and the `wetzel_*` variants for Erdős's [Er64g] resolution of the countable
analogue (Wetzel's problem), which this problem generalizes.
-/
def ErdosProblem1119Statement : Prop :=
  ∀ (𝔪 : Cardinal), ℵ₀ < 𝔪 → 𝔪 < continuum →
    ∀ (ι : Type) (f : ι → ℂ → ℂ),
      (∀ i, Differentiable ℂ (f i)) →
      (∀ z : ℂ, mk ↥(range (fun i => f i z)) ≤ 𝔪) →
      mk ↥(range f) ≤ 𝔪

/--
The 'easy' case of Erdős Problem #1119 (recorded in [Ha74]: "it is 'easy to
see' the answer is yes if 𝔪⁺ < 𝔠"): if the successor cardinal of 𝔪 is still
below the continuum, then any family of entire functions taking at most 𝔪
distinct values at every point contains at most 𝔪 distinct functions.

(Sketch of why this is ZFC-provable: given 𝔪⁺ distinct entire functions, the
pairwise agreement sets are countable — two distinct entire functions agree
on a set with no accumulation point — so their union over all 𝔪⁺ ⬝ 𝔪⁺ = 𝔪⁺
pairs has size at most 𝔪⁺ < 𝔠, and any z₀ outside it witnesses 𝔪⁺ > 𝔪
distinct values.)

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1119.variants.easy_case (𝔪 : Cardinal) (h1 : ℵ₀ < 𝔪)
    (h2 : Order.succ 𝔪 < continuum)
    (ι : Type) (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hval : ∀ z : ℂ, mk ↥(range (fun i => f i z)) ≤ 𝔪) :
    mk ↥(range f) ≤ 𝔪 :=
  sorry

/--
Erdős [Er64g], answering a question of Wetzel (the countable analogue of
Problem #1119, affirmative direction): if 𝔠 > ℵ₁, then a family of entire
functions with only countably many distinct values at each point z₀ ∈ ℂ is
itself countable.

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1119.variants.wetzel_yes (h : aleph 1 < continuum)
    (ι : Type) (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hval : ∀ z : ℂ, mk ↥(range (fun i => f i z)) ≤ ℵ₀) :
    mk ↥(range f) ≤ ℵ₀ :=
  sorry

/--
Erdős [Er64g], negative direction under CH: if 𝔠 = ℵ₁ then the countable
analogue fails — there is a family of entire functions, with only countably
many distinct values at each point, containing uncountably many distinct
functions. (Erdős's construction produces such a family of cardinality
𝔠 = ℵ₁.)

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1119.variants.wetzel_ch_counterexample
    (h : continuum = aleph 1) :
    ∃ (ι : Type) (f : ι → ℂ → ℂ),
      (∀ i, Differentiable ℂ (f i)) ∧
      (∀ z : ℂ, mk ↥(range (fun i => f i z)) ≤ ℵ₀) ∧
      ℵ₀ < mk ↥(range f) :=
  sorry

end Erdos1119
