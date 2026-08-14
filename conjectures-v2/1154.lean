import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section

open MeasureTheory

/-!
# Erdős Problem #1154

Does there exist, for every α ∈ [0,1], a ring or field in ℝ with Hausdorff
dimension α?

Verbatim source statement (erdosproblems.com/1154): "Does there exist, for
every $\alpha \in [0,1]$, a ring or field in $\mathbb{R}$ with Hausdorff
dimension $\alpha$?"

Status: OPEN per erdosproblems.com/1154, with the special banner
"NOT DISPROVABLE" (tooltip: "Open in general, but there exist models of set
theory where the result is true."), plus the owner's standard disclaimer.
Page last edited 25 January 2026, accessed 2026-02-23. Source line:
#1154: [Er79h, p.119] [Va99, 2.48].

Remarks from the source page:

* Erdős and Volkmann [ErVo66] proved that, for any α ∈ [0,1], there exists
  a group of real numbers of Hausdorff dimension α. (Formalized below as
  `erdos_problem_1154.variants.erdos_volkmann_subgroup`.)
* Falconer [Fa84] proved that any subring with Hausdorff dimension
  α ∈ (1/2,1) cannot be a Borel or Suslin set. Edgar and Miller [EdMi01]
  proved that any real closed analytic subfield of ℝ has Hausdorff dimension
  either 0 or 1. Later the same authors [EdMi03] proved that any subring of
  ℝ which is Borel or analytic either has Hausdorff dimension 0 or is equal
  to ℝ. (The Borel case of [EdMi03], which subsumes the Borel case of
  [Fa84], is formalized below as
  `erdos_problem_1154.variants.edgar_miller_borel`; the analytic/Suslin
  halves and the real-closed [EdMi01] statement are not formalized — they
  would need `MeasureTheory.AnalyticSet` and a real-closed-field predicate,
  outside this file's import surface.)
* Mauldin [Ma16b] proved that subfields of ℝ exist with Hausdorff dimension
  any α ∈ [0,1] assuming the continuum hypothesis. (Formalized below as
  `erdos_problem_1154.variants.mauldin_subfield_ch`.)

Encoding notes:

* The source poses a yes/no question and the problem is OPEN; this raw
  corpus has no `answer()` elaborator (Mathlib-only imports), and its
  uniform convention for open yes/no questions is a direct assertion of the
  asked ("yes") direction with a `sorry` proof, as here. In styled question
  form it would be `answer(sorry) ↔ ∀ α, …` (the archived styled copy of
  this problem uses exactly that shape over this same proposition).
* "A ring or field in ℝ": since every subfield is a subring, the literal
  disjunctive reading ("there is a ring or a field of dimension α") is
  equivalent to the subring statement, which is what `erdos_problem_1154`
  asserts. The field version is a genuinely stronger separate question,
  explicitly present in the source wording and in Mauldin's [Ma16b] partial
  result; it is formalized as `erdos_problem_1154.variants.subfield` (the
  first pass silently narrowed the docstring to "a subring of ℝ" and
  dropped the field half without note).
* Mathlib's `Subring` requires a multiplicative identity, while the rings
  in this literature (Falconer, Edgar–Miller) need not contain 1. The two
  readings give *equivalent* existence questions for every α: if R ⊆ ℝ is
  a rng (additive subgroup closed under multiplication) with dimH R = α,
  then S = R + ℤ = ⋃_{n ∈ ℤ} (R + n) is a unital subring — closed under
  multiplication since (r+m)(r'+m') = (rr' + mr' + m'r) + mm' — and
  dimH S = dimH R because Hausdorff dimension is translation-invariant and
  countably stable. Conversely every unital subring is a rng. So `Subring`
  is a faithful encoding.
* `dimH` returns `ℝ≥0∞`; `ENNReal.ofReal α` is the standard embedding and
  is faithful on the hypothesis range 0 ≤ α (no clamping). The restriction
  α ∈ [0,1] matches the source and is exactly the achievable range, since
  every subset of ℝ has dimH ≤ dimH(univ) = 1.
* Non-vacuity: the endpoints are genuinely realizable (α = 0 by the
  countable subring ℤ, α = 1 by ⊤ = ℝ itself, whose carrier is `univ`);
  the content lies in α ∈ (0,1), where [EdMi03] forces any witness to be
  non-Borel, non-analytic — hence the "NOT DISPROVABLE"/set-theoretic
  flavor of the problem.

Tags (per the page): analysis.
Formalised statement (per the page, as of access): No.
The page records 1 forum comment, no OEIS entries, and "Additional thanks
to: Quanyu Tang".

References (honest stubs; journal names and page ranges are from the
log-recovered `/latex/1154` extraction, which carries **no volume numbers**
— none are fabricated here):

[Er79h] Erdős, P. (1979), p. 119 — cited by the page as a problem source.
  No bibliographic expansion is recoverable from the logs: the `/latex/1154`
  extraction contains no [Er79h] entry. (The archived styled copy glossed
  this key as "_Some unconventional problems in number theory_. Math. Mag.
  52 (1979), p. 119" — an unsupported attribution that is also internally
  impossible, since that paper spans pp. 67–70; the gloss is not reproduced
  here. A reviewer-knowledge candidate, unverified against the site: Erdős,
  _Set theoretic, measure theoretic, combinatorial, and number theoretic
  problems concerning point sets in Euclidean space_, Real Anal. Exchange 4
  (1978/79), 113–138, whose page range contains p. 119 and whose subject
  matches.)

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999), §2.48. (Corpus-canonical identity of this site-global key,
  settled by the log-recovered `/latex/1005` and `/latex/1151` extractions
  and sibling reviews 1068, 1131–1153; the neighbouring problems 1151,
  1152, 1132 and 1153 cite §2.41–§2.44 of the same booklet. The archived
  styled copy and prior review glossed [Va99] as "Varga, R.S., _Scientific
  Computation on Mathematical Problems and Conjectures_" — a hallucinated
  attribution, not reproduced here; the `/latex/1154` fetch captured in the
  logs explicitly reported no [Va99] entry.)

[ErVo66] Erdős, P. and Volkmann, B., _Additive Gruppen mit vorgegebener
  Hausdorffscher Dimension_. J. Reine Angew. Math. (1966), 203–208.

[Fa84] Falconer, K. J., _Rings of fractional dimension_. Mathematika
  (1984), 25–27.

[EdMi01] Edgar, G. A. and Miller, C., _Hausdorff dimension, analytic sets
  and transcendence_. Real Anal. Exchange (2001/02), 335–339.

[EdMi03] Edgar, G. A. and Miller, C., _Borel subrings of the reals_. Proc.
  Amer. Math. Soc. (2003), 1121–1129.

[Ma16b] Mauldin, R. D., _Subfields of ℝ with arbitrary Hausdorff
  dimension_. Math. Proc. Cambridge Philos. Soc. (2016), 157–165.
-/

/--
Erdős Problem #1154 [Er79h, p.119] [Va99, 2.48] (Open — "not disprovable":
there exist models of set theory where the result is true):

Does there exist, for every α ∈ [0,1], a ring or field in ℝ with Hausdorff
dimension α?

This theorem asserts the "yes" direction of the open question for the ring
reading, per this corpus's convention for open yes/no questions (in styled
question form it would be `answer(sorry) ↔ …`); since every subfield is a
subring, this is also the literal disjunctive "ring or field" reading. The
field version proper is `erdos_problem_1154.variants.subfield`.

Erdős and Volkmann [ErVo66] proved the analogous result for subgroups of ℝ.
Falconer [Fa84] showed that any subring with Hausdorff dimension
α ∈ (1/2,1) cannot be Borel or Suslin. Edgar and Miller [EdMi03] proved
that any Borel or analytic subring of ℝ either has Hausdorff dimension 0 or
equals ℝ. Mauldin [Ma16b] proved the result for subfields assuming the
continuum hypothesis.
-/
theorem erdos_problem_1154 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ S : Subring ℝ, dimH (↑S : Set ℝ) = ENNReal.ofReal α :=
  sorry

/--
The field half of Erdős Problem #1154 [Er79h, p.119] [Va99, 2.48] (Open —
solved affirmatively under CH by Mauldin [Ma16b], see
`erdos_problem_1154.variants.mauldin_subfield_ch`):

Does there exist, for every α ∈ [0,1], a subfield of ℝ with Hausdorff
dimension α? Stated in the "yes" direction per the corpus convention for
open yes/no questions. This strengthens `erdos_problem_1154`, since every
subfield is a subring.
-/
theorem erdos_problem_1154.variants.subfield (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ S : Subfield ℝ, dimH (↑S : Set ℝ) = ENNReal.ofReal α :=
  sorry

/--
The page's first remark, proved by Erdős and Volkmann [ErVo66]: for any
α ∈ [0,1], there exists a group of real numbers (an additive subgroup of ℝ)
of Hausdorff dimension α. This is the solved subgroup analogue of the open
subring question.
-/
theorem erdos_problem_1154.variants.erdos_volkmann_subgroup
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ G : AddSubgroup ℝ, dimH (↑G : Set ℝ) = ENNReal.ofReal α :=
  sorry

/--
The Borel case of Edgar and Miller's theorem [EdMi03]: any subring of ℝ
which is Borel either has Hausdorff dimension 0 or is equal to ℝ. (On ℝ,
`MeasurableSet` is Borel measurability, since `Real.measurableSpace` is the
Borel σ-algebra. The analytic half of [EdMi03] — and hence the Suslin case
of Falconer's earlier bound [Fa84], whose Borel case this theorem subsumes
— is not formalized; it would need `MeasureTheory.AnalyticSet`, outside
this file's import surface.)

Consequently any witness to `erdos_problem_1154` with dimension α ∈ (0,1)
must be non-Borel, which is why the problem has the "not disprovable"
set-theoretic character.
-/
theorem erdos_problem_1154.variants.edgar_miller_borel
    (S : Subring ℝ) (hS : MeasurableSet (S : Set ℝ)) :
    dimH (S : Set ℝ) = 0 ∨ (S : Set ℝ) = Set.univ :=
  sorry

/--
The page's final remark, proved by Mauldin [Ma16b]: assuming the continuum
hypothesis, subfields of ℝ exist with Hausdorff dimension any α ∈ [0,1].
CH is taken as the hypothesis `ℵ₁ = 𝔠`, stated via `Cardinal.aleph` and
`Cardinal.continuum` (= 2^ℵ₀). This resolves
`erdos_problem_1154.variants.subfield` — and hence `erdos_problem_1154` —
affirmatively in models of CH, which is the content of the page's
"NOT DISPROVABLE" banner.
-/
theorem erdos_problem_1154.variants.mauldin_subfield_ch
    (hCH : Cardinal.aleph 1 = Cardinal.continuum)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ S : Subfield ℝ, dimH (↑S : Set ℝ) = ENNReal.ofReal α :=
  sorry

end
