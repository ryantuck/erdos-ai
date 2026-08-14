import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Data.Set.Card

/-!
# Erdős Problem #1127

Source: https://www.erdosproblems.com/1127 (page last edited 30 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Can $\mathbb{R}^n$ be decomposed into countably many sets,
such that within each set all the pairwise distances are distinct?"

Status: **INDEPENDENT** (banner tooltip: "Independent of the usual axioms of
set theory (ZFC)."). Problem source: [Er81b, p.31]. Tags: geometry, distances,
set theory.

Remarks from the page (verbatim, including the site's "statemant" typo):

* "This is true (assuming the continuum hypothesis) when $n=1$, since Erdős
  and Kakutani [ErKa43] proved that in fact the continuum hypothesis is
  equivalent to the statemant that $\mathbb{R}$ can be written as the union of
  countably many sets, each of which is linearly independent over
  $\mathbb{Q}$."
* "Davies [Da72] proved this true when $n=2$, and Kunen [Ku87] proved it is
  true for all $n$ (again, both assuming the continuum hypothesis)."
* "The dependence on the continuum hypothesis is necessary, since Erdős and
  Hajnal proved that if the continuum hypothesis is false then e.g. in any
  decomposition of $\mathbb{R}$ into finitely many sets there exist four
  points which determine only four distances."

Encoding notes:

* The problem is a yes/no question whose answer is INDEPENDENT of ZFC: under
  CH the decomposition exists for every $n$ (Kunen [Ku87]), and if CH fails it
  does not exist even for $n = 1$ (Erdős–Hajnal; this is what the page's
  "dependence on the continuum hypothesis is necessary" records, and why the
  banner reads INDEPENDENT rather than OPEN or PROVED). CH is likewise
  independent of Lean's type theory, so neither the affirmative nor the
  negative direction is provable in this corpus. The first-pass file asserted
  the affirmative direction as a bare theorem (`erdos_problem_1127 (n : ℕ) :
  ∃ f, …`), which is an unprovable claim and contradicts its own docstring's
  "(Independent of ZFC)". Following the treatment of problem #1119 (the same
  answer-shape situation), the question's content is recorded below as
  `Prop`-valued definitions (`DistinctDistanceDecomp`,
  `ErdosProblem1127Statement`), and the ZFC-provable parts of the problem's
  resolution — Kunen's CH-conditional theorem (kept under the original name
  `erdos_problem_1127`), the Erdős–Kakutani equivalence, the Erdős–Hajnal
  countable-decomposition result, and the resulting necessity of CH — are
  formalized as theorems.
* Two of the page's remark statements are literally defective as written and
  are formalized here in corrected form, with the corrections documented in
  the respective docstrings:
  1. the Erdős–Kakutani equivalence as quoted ("$\mathbb{R}$ can be written
     as the union of countably many sets, each of which is linearly
     independent over $\mathbb{Q}$") is falsified by $0$ alone — every set
     containing $0$ is $\mathbb{Q}$-linearly dependent, and $0$ must lie in
     some member of any cover of $\mathbb{R}$ — so the cover is required of
     $\mathbb{R}\setminus\{0\}$, the standard reading;
  2. the Erdős–Hajnal remark's "decomposition of $\mathbb{R}$ into *finitely*
     many sets" is trivially true in ZFC with no hypothesis on CH (restrict
     any finite coloring to $\mathbb{N}$ and take a monochromatic 4-term
     arithmetic progression via van der Waerden: it determines only 3
     distances), so it cannot express CH-necessity; the intended and
     literature-standard statement is for *countably* many sets, which is
     what is formalized.
* "Decomposed into countably many sets" is encoded by a coloring
  `f : … → ℕ`; color classes may be empty, so decompositions into finitely
  many sets are included, and a coloring is interchangeable with a countable
  cover (pass to the partition by least index; subsets of
  distance-injective/independent sets retain the property).
* Dimension $n = 0$ is included and harmless: `EuclideanSpace ℝ (Fin 0)` is a
  one-point space, so `DistinctDistanceDecomp 0` holds trivially.
* NOTE: none of the statements below are compile-verified (no `lake build` in
  the review container); in particular the import paths for
  `LinearIndependent` and `Set.ncard` should be checked (recent Mathlib
  splits `Mathlib.LinearAlgebra.LinearIndependent` into
  `…LinearIndependent.Defs` etc.).

References (citation keys as on the archived page; [ErKa43]/[Da72]/[Ku87]
bibliographic data recovered from the original pipeline's fetch of
erdosproblems.com/latex/1127, which carried authors, titles, journals, years
and pages but NO volume numbers — the volumes marked (*) are carried from the
archived styled sibling `deepmind/deepmind/1127.lean` and agree with reviewer
knowledge, but are NOT site-verified):

[ErKa43] Erdős, P. and Kakutani, S., _On non-denumerable graphs_, Bull. Amer.
Math. Soc. 49 (*) (1943), 457-461.

[Da72] Davies, Roy O., _Partitioning the plane into denumerably many sets
without repeated distances_, Proc. Cambridge Philos. Soc. 72 (*) (1972),
179-183.

[Ku87] Kunen, Kenneth, _Partitioning Euclidean space_, Math. Proc. Cambridge
Philos. Soc. 102 (*) (1987), 379-383.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981),
27-35. (Not present in the `/latex/1127` extraction — the upstream pipeline
noted "The LaTeX source doesn't have [Er81b]" — carried from the site's
`/latex/1123` bibliography as recovered for the sibling problem #1123, which
uses the same key with [Er81b, p.30]; the p.31 citation here falls in the
same 27-35 page range. NOT verified against /latex/1127.)

The Erdős–Hajnal necessity result is attributed on the page by name only, with
no citation key; no reference is invented for it here.

Related OEIS sequences: none listed. Formalised statement in external
databases: No (as of the archived capture). The page records 0 comments.
Previous problem: #1126; next problem: #1128. The first-pass input file
`conjectures/1127.lean` built successfully against this repo's Mathlib
(2388 jobs, sole warning the expected `sorry`).
-/

/--
`DistinctDistanceDecomp n` says: ℝⁿ (as `EuclideanSpace ℝ (Fin n)`) can be
decomposed into countably many sets, such that within each set all the
pairwise distances are distinct.

The decomposition is a coloring `f : ℝⁿ → ℕ`; the distinct-distance condition
says that whenever four points of one color class form two pairs `{a, b}` and
`{c, d}` of distinct points at equal distance, the pairs coincide as unordered
pairs — equivalently, distinct unordered pairs within a class always have
distinct distances.
-/
def DistinctDistanceDecomp (n : ℕ) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin n) → ℕ,
    ∀ a b c d : EuclideanSpace ℝ (Fin n),
      f a = f b → f a = f c → f a = f d →
      a ≠ b → c ≠ d →
      dist a b = dist c d →
      ({a, b} : Set (EuclideanSpace ℝ (Fin n))) = {c, d}

/--
Erdős Problem #1127 [Er81b, p.31]:

Can ℝⁿ be decomposed into countably many sets, such that within each set all
the pairwise distances are distinct?

This `Prop` is the affirmative answer for every dimension simultaneously. It
is recorded as a definition rather than asserted as a theorem because it is
INDEPENDENT of ZFC (and of Lean's type theory): it holds under the continuum
hypothesis (Kunen [Ku87], `erdos_problem_1127` below) and fails if the
continuum hypothesis fails (Erdős–Hajnal,
`erdos_problem_1127.variants.necessity` below).
-/
def ErdosProblem1127Statement : Prop :=
  ∀ n : ℕ, DistinctDistanceDecomp n

/--
Kunen [Ku87], the CH-conditional affirmative resolution of Erdős Problem
#1127: assuming the continuum hypothesis (𝔠 = ℵ₁), for every n the space ℝⁿ
can be decomposed into countably many sets, such that within each set all the
pairwise distances are distinct.

The n = 1 case is due to Erdős and Kakutani [ErKa43] (via
`erdos_problem_1127.variants.erdos_kakutani`: a ℚ-linearly independent set has
all pairwise distances distinct) and the n = 2 case to Davies [Da72]. The CH
hypothesis cannot be dropped: see `erdos_problem_1127.variants.necessity`.

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1127 (hCH : Cardinal.continuum = Cardinal.aleph 1)
    (n : ℕ) : DistinctDistanceDecomp n :=
  sorry

/--
Erdős–Kakutani [ErKa43]: the continuum hypothesis is equivalent to the
statement that ℝ (minus the origin) can be written as the union of countably
many sets, each of which is linearly independent over ℚ.

The page quotes the equivalence for "ℝ"; the cover here is required of
ℝ \ {0} because no set containing 0 is ℚ-linearly independent, so the literal
version with a cover of all of ℝ is false in ZFC for that degenerate reason —
excluding 0 is the standard reading (0 can always be given its own class,
which even preserves the distinct-distance property).

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1127.variants.erdos_kakutani :
    Cardinal.continuum = Cardinal.aleph 1 ↔
      ∃ S : ℕ → Set ℝ,
        (∀ x : ℝ, x ≠ 0 → ∃ k, x ∈ S k) ∧
        ∀ k, LinearIndependent ℚ ((↑) : S k → ℝ) :=
  sorry

/--
Erdős–Hajnal (as recorded on the problem page): if the continuum hypothesis is
false, then in any decomposition of ℝ into countably many sets there exist
four points (of a single class) which determine only four distances — i.e.
four pairwise-distinct points of one color class whose six pairwise distances
take at most four values.

The page's phrasing says "decomposition of ℝ into *finitely* many sets", but
that statement is trivially true in ZFC without any set-theoretic hypothesis
(any finite coloring of ℝ colors ℕ with finitely many colors, and a
monochromatic 4-term arithmetic progression a, a+t, a+2t, a+3t — van der
Waerden — determines only the three distances t, 2t, 3t), so it cannot carry
the CH-necessity the page invokes it for; the intended statement, formalized
here, is for countable decompositions. (A same-class solution of
x₁ - x₂ = x₃ - x₄ in distinct reals yields the two coincidences
|x₁ - x₂| = |x₃ - x₄| and |x₁ - x₃| = |x₂ - x₄|, hence at most four distinct
values among the six distances — the classical form of the Erdős–Hajnal
result.)

NOTE: statement written from the recovered source page with the correction
documented above; not compile-verified.
-/
theorem erdos_problem_1127.variants.erdos_hajnal
    (h : Cardinal.aleph 1 < Cardinal.continuum) (f : ℝ → ℕ) :
    ∃ x₁ x₂ x₃ x₄ : ℝ,
      f x₁ = f x₂ ∧ f x₁ = f x₃ ∧ f x₁ = f x₄ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₁ ≠ x₄ ∧ x₂ ≠ x₃ ∧ x₂ ≠ x₄ ∧ x₃ ≠ x₄ ∧
      ({dist x₁ x₂, dist x₁ x₃, dist x₁ x₄,
        dist x₂ x₃, dist x₂ x₄, dist x₃ x₄} : Set ℝ).ncard ≤ 4 :=
  sorry

/--
Necessity of the continuum hypothesis for Erdős Problem #1127 ("The dependence
on the continuum hypothesis is necessary"): if the continuum hypothesis fails,
then already ℝ¹ admits no decomposition into countably many sets with all
pairwise distances distinct within each set.

This follows from `erdos_problem_1127.variants.erdos_hajnal`: four distinct
points of one class with at most four distinct values among their six pairwise
distances yield two distinct unordered pairs at equal distance (pigeonhole),
contradicting the distinct-distance property (`EuclideanSpace ℝ (Fin 1)` is
isometric to ℝ). Together with `erdos_problem_1127` this makes
`ErdosProblem1127Statement` equivalent to the continuum hypothesis, hence
independent of ZFC — the page's INDEPENDENT status.

NOTE: statement written from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1127.variants.necessity
    (h : Cardinal.aleph 1 < Cardinal.continuum) :
    ¬ DistinctDistanceDecomp 1 :=
  sorry
