import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1134

Let A ⊆ ℕ be the smallest set which contains 1 and is closed under the
operations x ↦ 2x+1, x ↦ 3x+1, and x ↦ 6x+1. Does A have positive
lower density?

Status on erdosproblems.com/1134: DISPROVED ("This has been solved in the
negative."); prize banner "$24". Page last edited 09 January 2026, accessed
2026-02-23. Tag: number theory. Related OEIS sequence: A185661.

History (page remarks): Lagarias [La16] reports that Erdős asked this in
1972, offering £10 for a solution (although Hilton told Lagarias that this
problem may have been formulated by Klarner, and that Erdős liked it and
offered a prize for its solution).

Erdős had earlier proved (as reported in [KlRa74]) that if A is the smallest
set which contains 1 and is closed under the operations x ↦ mᵢx + bᵢ for
some (possibly infinite) collection of mᵢ ≥ 1 and bᵢ ≥ 0 then, if σ > 0 is
such that ∑ 1/mᵢ^σ = 1, then for all large X, |A ∩ [1,X]| ≪ X^{σ+o(1)}.
This result does not help with the given problem since 1/2 + 1/3 + 1/6 = 1.

The question was answered in the negative soon afterwards by Crampin and
Hilton (as reported in [Kl82]), who proved that in fact, for all large X,
|A ∩ [1,X]| ≪ X^{τ+o(1)}, where τ < 1 is the unique positive root of
6^{-τ} + ∑_{k≥0} (3·2^k)^{-τ} = 1. Their proof is given in [La16]. Since
τ < 1, the natural density of A is 0 — the main statement below — and in
particular A does not have positive lower density (the question as asked,
stated as a variant below).

(Constant caveat: the page states τ ≈ 0.900626, but high-precision
computation of the page's own displayed equation, i.e. of
6^{-τ} + 3^{-τ}/(1 - 2^{-τ}) = 1, gives τ = 0.9005264428…, so the page's
constant and equation disagree in the fourth decimal; one of the two carries
a typo. [La16] is unreachable offline, so which is wrong is left undecided.
Either way τ < 1, and the constant does not enter any formal statement.)

Klarner has several open variants of this problem — see Section 8.9 of
[La16]. For example, it is unknown if the smallest set which contains 0 and
is closed under x ↦ 2x, x ↦ 3x+2, and x ↦ 6x+3 has positive density
(formalized below). That problem is repeated by Guy [Gu83b] in an article
called 'Don't Try to Solve These Problems', and is Problem E36 in Guy's
collection [Gu04].

References (authors, titles, journals, years, and pages recovered from the
original pipeline's fetch of erdosproblems.com/latex/1134 preserved in the
session logs; volume numbers were absent from the recovered extraction and
are deliberately not invented):

- [La16] Lagarias, J. C., _Erdős, Klarner, and the 3x+1 problem_. American
  Mathematical Monthly (2016), 753–776.
- [KlRa74] Klarner, D. A. and Rado, R., _Arithmetic properties of certain
  recursively defined sets_. Pacific Journal of Mathematics (1974), 445–463.
- [Kl82] Klarner, D. A., _A sufficient condition for certain semigroups to
  be free_. Journal of Algebra (1982), 140–148.
- [Gu83b] Guy, R. K., _Unsolved Problems: Don't Try to Solve These
  Problems_. American Mathematical Monthly (1983), 35–38 and 39–41.
- [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.

NOTE: the main statement below is unchanged from the input file
(`conjectures/1134.lean`) except for dropping a redundant `Finset.`
qualification under the existing `open Finset` — the Fable review of
2026-08-14 found no semantic defects in it. The bibliography, the τ caveat,
and the two page-confirmed variants were added by that review and are NOT
compile-verified (the review container cannot run `lake build`).
-/

/-- The set A from Erdős Problem #1134: the smallest subset of ℕ containing 1
    and closed under x ↦ 2x+1, x ↦ 3x+1, and x ↦ 6x+1. -/
inductive Erdos1134.InSet : ℕ → Prop where
  | base : Erdos1134.InSet 1
  | step2 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (2 * n + 1)
  | step3 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (3 * n + 1)
  | step6 (n : ℕ) : Erdos1134.InSet n → Erdos1134.InSet (6 * n + 1)

noncomputable instance : DecidablePred Erdos1134.InSet := Classical.decPred _

/-- The counting function: |A ∩ [1, N]| for the set A from Problem #1134. -/
noncomputable def Erdos1134.count (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => Erdos1134.InSet n)).card

/--
Erdős Problem #1134 [La16][KlRa74][Kl82][Gu83b][Gu04]:

Let A ⊆ ℕ be the smallest set containing 1 and closed under x ↦ 2x+1,
x ↦ 3x+1, and x ↦ 6x+1. Then A does not have positive lower density;
in fact the natural density of A is 0 (the statement formalized here, which
is strictly stronger than the literal negative answer — see the variant
below for the question as asked).

Disproved (answered in the negative) by Crampin and Hilton (reported in
[Kl82], proof in [La16]), who showed |A ∩ [1,X]| ≪ X^{τ+o(1)} where
τ < 1 is the unique positive root of 6^{-τ} + ∑_{k≥0} (3·2^k)^{-τ} = 1
(≈ 0.9005; the source page prints 0.900626 — see the module docstring).
-/
theorem erdos_problem_1134 :
    Tendsto (fun N : ℕ => (Erdos1134.count N : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
  sorry

/--
Variant — the question exactly as asked on the page, with its (negative)
answer: A does NOT have positive lower density, i.e. there is no c > 0 with
|A ∩ [1,N]| ≥ cN for all large N. Since count N / N ≥ 0, this is equivalent
to liminf count N / N = 0, and it follows from the main statement
`erdos_problem_1134` (density 0 forces the liminf to be 0). Disproved by
Crampin and Hilton [Kl82][La16].

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1134.variants.not_pos_lower_density :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ (N : ℕ) in atTop, c ≤ (Erdos1134.count N : ℝ) / (N : ℝ) :=
  sorry

/-- The set B from Klarner's variant of Erdős Problem #1134: the smallest
    subset of ℕ containing 0 and closed under x ↦ 2x, x ↦ 3x+2, and
    x ↦ 6x+3. -/
inductive Erdos1134.InSetKlarner : ℕ → Prop where
  | base : Erdos1134.InSetKlarner 0
  | step2 (n : ℕ) : Erdos1134.InSetKlarner n → Erdos1134.InSetKlarner (2 * n)
  | step3 (n : ℕ) : Erdos1134.InSetKlarner n → Erdos1134.InSetKlarner (3 * n + 2)
  | step6 (n : ℕ) : Erdos1134.InSetKlarner n → Erdos1134.InSetKlarner (6 * n + 3)

noncomputable instance : DecidablePred Erdos1134.InSetKlarner :=
  Classical.decPred _

/-- The counting function |B ∩ [1, N]| for Klarner's variant. (B also
    contains 0, which is irrelevant for density.) -/
noncomputable def Erdos1134.countKlarner (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (fun n => Erdos1134.InSetKlarner n)).card

/--
Variant (Klarner, OPEN — page remark, Section 8.9 of [La16]; repeated by Guy
[Gu83b], Problem E36 in [Gu04]): does the smallest set B ⊆ ℕ containing 0
and closed under x ↦ 2x, x ↦ 3x+2, and x ↦ 6x+3 have positive density?

Stated as a direct assertion of the asked ("yes") direction per this
corpus's raw-file convention for open questions; a styled version would use
the `answer(sorry) ↔` question form. The page's "positive density" is
encoded as positive LOWER density (∃ c > 0 with |B ∩ [1,N]| ≥ cN for all
large N), matching the density notion of the main problem; if the natural
density of B exists, the two readings agree.

NOTE: added by the Fable review of 2026-08-14 from the recovered source
page; not compile-verified.
-/
theorem erdos_problem_1134.variants.klarner_pos_density :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ (N : ℕ) in atTop, c ≤ (Erdos1134.countKlarner N : ℝ) / (N : ℝ) :=
  sorry

end
