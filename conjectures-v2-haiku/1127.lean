import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.SetTheory.Cardinal.Continuum

/--
Erdős Problem #1127 (Independent of ZFC)

Verbatim statement from erdosproblems.com:
"Can ℝⁿ be decomposed into countably many sets, such that within each set all the
pairwise distances are distinct?"

Status: INDEPENDENT of ZFC. The problem's answer depends on the continuum hypothesis:
- TRUE under CH: Erdős and Kakutani proved it for n = 1 (via a CH-equivalence with
  decompositions into ℚ-linearly independent sets [ErKa43]). Davies proved it for
  n = 2 [Da72]. Kunen proved it for all n [Ku87].
- FALSE under ¬CH: Erdős and Hajnal proved the continuum hypothesis is necessary —
  if CH fails, no such decomposition of ℝ exists, even for n = 1.

The statement is thus equivalent to CH over ZFC and is neither provable nor refutable
in Lean's type theory (where CH is also independent via the standard forcing/inner-model
arguments). The encoding below records the decomposition property as a `Prop`-valued
definition and formalizes the ZFC-provable resolution: Kunen's CH-conditional theorem,
the Erdős–Kakutani CH-equivalence, the Erdős–Hajnal necessity result, and the resulting
CH-equivalence of the full statement.

Remarks from the source page (verbatim, including the site's "statemant" typo):

* "This is true (assuming the continuum hypothesis) when n=1, since Erdős and Kakutani
  [ErKa43] proved that in fact the continuum hypothesis is equivalent to the statemant
  that ℝ can be written as the union of countably many sets, each of which is linearly
  independent over ℚ."
* "Davies [Da72] proved this true when n=2, and Kunen [Ku87] proved it is true for
  all n (again, both assuming the continuum hypothesis)."
* "The dependence on the continuum hypothesis is necessary, since Erdős and Hajnal
  proved that if the continuum hypothesis is false then e.g. in any decomposition of
  ℝ into finitely many sets there exist four points which determine only four distances."

(Note: the Erdős–Hajnal statement as quoted uses "finitely many sets", which is a ZFC
triviality — any finite coloring of ℝ colors ℕ finitely, and van der Waerden gives a
monochromatic 4-term AP determining only 3 distances. The intended and literature-standard
statement, formalized below, is for countably many sets.)

Formalization notes:
- A decomposition into countably many sets is encoded by a coloring f : ℝⁿ → ℕ;
  the preimages are the color classes. Non-surjective colorings (finite decompositions)
  are included, which is the standard reading.
- "All pairwise distances distinct within each set" is captured by the contrapositive:
  if two unordered pairs {a,b} and {c,d} in the same class have equal distance, the
  pairs coincide.
- Dimension n = 0: EuclideanSpace ℝ (Fin 0) is a one-point space, so the condition holds
  vacuously (no two distinct points).
- The problem cannot be formalized as a bare theorem asserting the affirmative
  unconditionally (that would be claiming a false statement is provable in Lean).
  Instead, the question content is recorded as definitions, and the resolvable pieces
  are theorems with CH hypotheses or consequences.

NOTE: the statements below are written from the recovered source page content and the
problem's mathematical literature. They are NOT compile-verified (this review container
has no Lean toolchain). The import of Mathlib.SetTheory.Cardinal.Continuum is assumed
to provide the necessary cardinal-arithmetic definitions and theorems; recent Mathlib
may require import splits (cf. .Defs suffixes). The statements use standard idioms
(existential quantifiers, set membership, linear independence) assumed to be available
in the current Mathlib version.

Citation keys recovered from the problem page and upstream session logs:

[ErKa43] Erdős, P. and Kakutani, S. _On non-denumerable graphs_. Bull. Amer. Math. Soc.
(1943). (Volume number not in the recovered /latex/1127 extraction.)

[Da72] Davies, Roy O. _Partitioning the plane into denumerably many sets without
repeated distances_. Proc. Cambridge Philos. Soc. (1972). (Volume not verified from
/latex extraction.)

[Ku87] Kunen, Kenneth. _Partitioning Euclidean space_. Math. Proc. Cambridge Philos.
Soc. (1987). (Volume not verified from /latex extraction.)

[Er81b] Referenced on page as [Er81b, p.31]; appears to be Erdős, P. _My Scottish Book
'Problems'_. The Scottish Book (1981), 27–35. (Not verified against /latex/1127 itself;
carried from cross-problem reference and upstream session-log artifact metadata.)

The Erdős–Hajnal necessity result is attributed by name on the page with no citation key;
no reference is invented here.
-/

/--
`DistinctDistanceDecomp n` records the property that ℝⁿ (as `EuclideanSpace ℝ (Fin n)`)
can be decomposed into countably many sets such that within each set all pairwise
distances are distinct.

Formally: there exists a coloring f : ℝⁿ → ℕ such that for every color class, whenever
two unordered pairs of points in that class have equal distance, the pairs coincide.
The contrapositive: distinct unordered pairs in the same color class have distinct
distances.
-/
def DistinctDistanceDecomp (n : ℕ) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin n) → ℕ,
    ∀ a b c d : EuclideanSpace ℝ (Fin n),
      f a = f b → f a = f c → f a = f d →
      a ≠ b → c ≠ d →
      dist a b = dist c d →
      ({a, b} : Set (EuclideanSpace ℝ (Fin n))) = {c, d}

/--
`ErdosProblem1127Statement` is the full yes/no question: can ℝⁿ be decomposed with
distinct pairwise distances for every dimension n simultaneously?

This `Prop` is recorded as a definition rather than asserted as a theorem because it is
INDEPENDENT of ZFC: it is equivalent to the continuum hypothesis. Under CH it is true
(Kunen's result, formalized as `erdos_problem_1127` with a CH hypothesis); without CH
it is false (Erdős–Hajnal necessity, formalized as `erdos_problem_1127.variants.necessity`).
Together, these make the full statement equivalent to CH, hence independent of ZFC
(and of Lean's type theory, where CH is also undecidable).
-/
def ErdosProblem1127Statement : Prop :=
  ∀ n : ℕ, DistinctDistanceDecomp n

/--
Kunen [Ku87]: Assuming the continuum hypothesis, for every n the space ℝⁿ can be
decomposed into countably many sets, such that within each set all the pairwise
distances are distinct.

This is the CH-conditional affirmative resolution of Erdős Problem #1127. The result
subsumes the earlier cases: Erdős and Kakutani [ErKa43] proved it for n = 1 (via a
deeper CH-equivalence with decompositions into ℚ-linearly independent sets — see
`variants.erdos_kakutani` below), and Davies [Da72] proved it for n = 2.

The continuum hypothesis is necessary (see `variants.necessity`); without CH, the
decomposition fails even for n = 1.

NOTE: not compile-verified.
-/
theorem erdos_problem_1127
    (hCH : Cardinal.continuum = Cardinal.aleph 1)
    (n : ℕ) : DistinctDistanceDecomp n :=
  sorry

/--
Erdős–Kakutani [ErKa43]: the continuum hypothesis is equivalent to the statement that
ℝ (minus the origin) can be written as the union of countably many sets, each of which
is linearly independent over ℚ.

**Correction:** The source page's quoted statement ("ℝ can be written as the union of
countably many sets, each of which is linearly independent over ℚ") is literally false
in ZFC: the zero element 0 ∈ ℝ lies in some member of any covering, and no set
containing 0 is ℚ-linearly independent (0 is a nontrivial rational combination of
itself). The standard mathematical reading, formalized here, covers ℝ \ {0}; zero can
always be assigned its own singleton class, which preserves the distinct-distance
property.

The deeper content of the Erdős–Kakutani result is that CH is not merely sufficient for
the distinct-distance decomposition of ℝ (n = 1 case of Kunen), but is *equivalent* to
the existence of the linearly-independent decomposition.

NOTE: not compile-verified. Mathlib's LinearIndependent assumes availability via
Mathlib.LinearAlgebra.LinearIndependent.Defs or similar; recent splits may require
adjusted imports.
-/
theorem erdos_problem_1127.variants.erdos_kakutani :
    Cardinal.continuum = Cardinal.aleph 1 ↔
      ∃ S : ℕ → Set ℝ,
        (∀ x : ℝ, x ≠ 0 → ∃ k, x ∈ S k) ∧
        ∀ k, LinearIndependent ℚ (fun x : S k => (x : ℝ)) :=
  sorry

/--
Erdős–Hajnal: if the continuum hypothesis is false, then in any decomposition of ℝ
into countably many sets there exist four distinct points of a single class whose six
pairwise distances take at most four distinct values.

**Correction:** The source page's literal statement says "decomposition of ℝ into
*finitely* many sets", but this is a ZFC triviality carrying no set-theoretic content:
any finite coloring of ℝ colors the integers finitely, and by van der Waerden's
theorem, a monochromatic 4-term arithmetic progression a, a+t, a+2t, a+3t determines
only the three distances t, 2t, 3t ≤ 4. This trivial version cannot express the CH-necessity
the page invokes it for. The standard and literature-correct statement, formalized here,
applies to countable decompositions. The classical reduction: if x₁, x₂, x₃, x₄ are
four distinct points of one color class with a same-class solution to x₁ - x₂ = x₃ - x₄,
then |x₁ - x₂| = |x₃ - x₄| and |x₁ - x₃| = |x₂ - x₄|, yielding at most four distinct
values among the six pairwise distances.

NOTE: not compile-verified. The statement uses `Set.ncard` (Mathlib.Data.Set.Card) for
cardinality of the distance set.
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
Necessity of the continuum hypothesis for Erdős Problem #1127 ("The dependence on the
continuum hypothesis is necessary"): if the continuum hypothesis fails, then already
ℝ¹ (i.e., n = 1) admits no decomposition into countably many sets with all pairwise
distances distinct within each set.

Proof sketch (in ZFC+¬CH): Suppose, for contradiction, that `DistinctDistanceDecomp 1`
holds, i.e., there exists a coloring f : ℝ → ℕ with the distinct-distance property.
By `variants.erdos_hajnal`, any such coloring under ¬CH has four same-class points whose
six distances take at most four values. By pigeonhole, two of the six distances are equal.
This means two distinct unordered pairs in the same class have equal distance, contradicting
the distinct-distance property. Hence ¬CH implies ¬`DistinctDistanceDecomp 1`.

Together with `erdos_problem_1127` (which says CH → all-$n$ distinct-distance decompositions
exist), this shows `ErdosProblem1127Statement ↔ CH`, proving the INDEPENDENT status.

NOTE: not compile-verified.
-/
theorem erdos_problem_1127.variants.necessity
    (h : Cardinal.aleph 1 < Cardinal.continuum) :
    ¬ DistinctDistanceDecomp 1 :=
  sorry
