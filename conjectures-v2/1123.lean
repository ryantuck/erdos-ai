import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Hom.Bounded
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Order.Basic

/-!
# Erdős Problem #1123

Source: https://www.erdosproblems.com/1123 (page last edited 31 December 2025;
full archived HTML capture accessed 2026-02-23; a second, structured capture
from 2026-03-15 reflects a later page edition — see the remarks below).

Verbatim statement: "Let $B_1$ be the Boolean algebra of sets of integers
modulo sets of density $0$ (that is, in which two sets are equivalent if and
only if they differ by a set of density $0$) and let $B_2$ be the Boolean
algebra of sets modulo sets of logarithmic density $0$.

Prove that $B_1$ and $B_2$ are not isomorphic."

Status: INDEPENDENT (banner tooltip: "Independent of the usual axioms of set
theory (ZFC)."), with a \$100 prize. Problem sources: [VMR80, p.238] (as
Question 48) and [Er81b, p.30]. Tag: algebra.

Remarks from the page (2026-02-23 capture):

* A question of Erdős and Ulam, who noted that the Boolean algebra modulo
  finite sets is not isomorphic to either of these two, "because the former
  has no upper bound while the other two do". (Formalized below as the two
  `erdos_problem_1123.variants.*` theorems.)
* They thought they had a proof of the main claim, but this was "lost". Erdős
  [Er81b] writes: "When I first visited Ulam in 1943 or 1944 in Madison we had
  the proof, then six months later we had forgotten the proof, and had to
  reconstruct it, so it seems that the proof should have been correct. Now the
  proof is gone and nobody can prove it. This problem should be settled;
  perhaps I should offer a hundred dollars for a proof (or a disproof) that
  these two Boolean algebras are not isomorphic. If it is trivial I well
  deserve to have to pay the hundred dollars."
* In fact Just and Krawczyk [JuKr84] proved, assuming the continuum
  hypothesis, that these two algebras ARE isomorphic. It is unclear whether
  this counts as a solution — in [JuKr84] they claim Erdős and Ulam asked
  about this only under the continuum hypothesis, but this is not mentioned in
  [Er81b].
* The question whether these two algebras are isomorphic appears in [VMR80] as
  Question 48, where it is attributed to Erdős, and there it is only asked
  about assuming the continuum hypothesis.
* (Later page edition, 2026-03-15 capture only:) Farah [Fa00, Corollary 3.4.4]
  proved, assuming the Open Coloring Axiom and Martin's Axiom, that $B_1$ and
  $B_2$ are NOT isomorphic; [ARS85] gives the consistency of OCA + MA with
  ZFC, which together with [JuKr84] establishes the ZFC-independence announced
  by the status banner.

Encoding notes.

1. The source poses the problem as a directive ("Prove that $B_1$ and $B_2$
   are not isomorphic"), so, per the corpus convention (this raw-file corpus
   has no `answer()` elaborator), the main theorem is a direct assertion of
   non-isomorphism — the direction Erdős asked for, and the direction that
   holds under OCA + MA [Fa00]. Because the proposition is independent of
   ZFC, the corresponding Lean statement is expected to be neither provable
   nor refutable from Mathlib's classical axioms; the `sorry` records the
   problem statement, not a truth claim.
2. "Sets of integers" is rendered as `Set ℕ`, the standard reading: all the
   references treat $\mathcal{P}(\omega)/I$ for ideals $I$ on $\omega$.
3. The quotients carry the inclusion-modulo-ideal order, defined concretely
   below: $[A] \le [B]$ iff $A \setminus B$ lies in the relevant ideal. This
   is the partial order of the quotient Boolean algebra, and since a Boolean
   algebra's operations (join, meet, complement, top, bottom) are determined
   by its order, an order isomorphism between the two quotients is exactly a
   Boolean-algebra isomorphism; hence `≃o` with respect to these concrete
   orders faithfully encodes "isomorphic as Boolean algebras". (The input
   file `conjectures/1123.lean` instead postulated the two `BooleanAlgebra`
   instances with `:= sorry`. A `sorry` in *data* position — as opposed to
   proof position — leaves the order on the quotients completely
   unspecified, so the non-isomorphism statement there did not pin down the
   Erdős–Ulam problem. This v2 removes every data-level `sorry`; the
   remaining `sorry`s are proof obligations of true propositions
   (ideal/well-definedness facts) or the problem statements themselves.)

References (keys as on the recovered page; bibliographic data recovered from
the site's `/latex/1123` bibliography via the session logs, except that
volume numbers were absent from the recovered extraction and are included
only where carried from the archived styled sibling
`deepmind/deepmind/1123.lean`, marked (*) — those are NOT site-verified):

[VMR80] van Douwen, E. K., Monk, J. D. and Rubin, M., _Some questions about
Boolean algebras_. Algebra Universalis 10 (*) (1980), 220-243.

[Er81b] Erdős, P., _My Scottish Book 'Problems'_. The Scottish Book (1981),
27-35 (2nd edition).

[JuKr84] Just, W. and Krawczyk, A., _On certain Boolean algebras
$\mathcal{P}(\omega)/I$_. Trans. Amer. Math. Soc. 285 (*) (1984), 411-429.

[ARS85] Abraham, U., Rubin, M. and Shelah, S., _On the consistency of some
partition theorems for continuous colorings, and the structure of
$\aleph_1$-dense real order types_. Ann. Pure Appl. Logic (1985), 123-206.

[Fa00] Farah, I., _Analytic quotients: theory of liftings for quotients over
analytic ideals on the integers_. Mem. Amer. Math. Soc. (2000), xvi+177.

Related OEIS sequences: none listed. Additional thanks to: Desmond
Weisenberg. Formalised statement in external databases: No (as of the
archived captures). The page records 2 comments (contents not captured).

NOTE: this v2 restatement is NOT compile-verified (no Lean toolchain in the
review container). The input `conjectures/1123.lean` is recorded as building
successfully on 2026-02-23 (session log 66b2bb9b, "Build completed
successfully (1894 jobs)").
-/

noncomputable section

open Filter Finset Classical BigOperators

/-- The natural (asymptotic) density of a set A ⊆ ℕ is zero if
    |A ∩ {0,...,n}| / (n+1) → 0 as n → ∞. -/
def HasNaturalDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    ((filter (· ∈ A) (range (n + 1))).card : ℝ) / ((n : ℝ) + 1))
    atTop (nhds 0)

/-- The logarithmic density of a set A ⊆ ℕ is zero if
    (1/log n) · Σ_{k ∈ A, 1 ≤ k ≤ n} 1/k → 0 as n → ∞. -/
def HasLogDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ =>
    (∑ k ∈ filter (· ∈ A) (Icc 1 n), (1 : ℝ) / (k : ℝ)) /
    Real.log (n : ℝ))
    atTop (nhds 0)

/-- Two sets of naturals are equivalent mod natural-density-0 sets
    iff their symmetric difference has natural density zero. -/
def NatDensityEquiv (A B : Set ℕ) : Prop :=
  HasNaturalDensityZero (symmDiff A B)

/-- Two sets of naturals are equivalent mod log-density-0 sets
    iff their symmetric difference has logarithmic density zero. -/
def LogDensityEquiv (A B : Set ℕ) : Prop :=
  HasLogDensityZero (symmDiff A B)

/-- The natural-density-zero sets form an ideal, so `NatDensityEquiv` is an
    equivalence relation. A true (ZFC-provable) proposition, recorded as a
    `sorry`d theorem — rather than as a `sorry` inside the `Setoid`
    definition, as in the input file — so that no `def` below contains
    `sorry`. NOTE: not compile-verified. -/
theorem natDensityEquiv_equivalence : Equivalence NatDensityEquiv :=
  sorry

/-- The log-density-zero sets form an ideal, so `LogDensityEquiv` is an
    equivalence relation. See `natDensityEquiv_equivalence`.
    NOTE: not compile-verified. -/
theorem logDensityEquiv_equivalence : Equivalence LogDensityEquiv :=
  sorry

/-- The equivalence relation on Set ℕ given by natural density zero. -/
def natDensitySetoid : Setoid (Set ℕ) where
  r := NatDensityEquiv
  iseqv := natDensityEquiv_equivalence

/-- The equivalence relation on Set ℕ given by logarithmic density zero. -/
def logDensitySetoid : Setoid (Set ℕ) where
  r := LogDensityEquiv
  iseqv := logDensityEquiv_equivalence

/-- B₁: the Boolean algebra of sets of integers modulo sets of natural density 0. -/
def BoolAlgModNatDensity : Type := Quotient natDensitySetoid

/-- B₂: the Boolean algebra of sets of integers modulo sets of logarithmic density 0. -/
def BoolAlgModLogDensity : Type := Quotient logDensitySetoid

/-- Whether `A \ B` has natural density zero depends only on the classes of
    `A` and `B` modulo `NatDensityEquiv` — well-definedness of the quotient
    order on B₁. A true proposition (the ideal property), `sorry`-recorded.
    NOTE: not compile-verified. -/
theorem natDensityLE_congr : ∀ A₁ B₁ A₂ B₂ : Set ℕ,
    NatDensityEquiv A₁ A₂ → NatDensityEquiv B₁ B₂ →
    HasNaturalDensityZero (A₁ \ B₁) = HasNaturalDensityZero (A₂ \ B₂) :=
  sorry

/-- Whether `A \ B` has logarithmic density zero depends only on the classes
    of `A` and `B` modulo `LogDensityEquiv` — well-definedness of the
    quotient order on B₂. A true proposition, `sorry`-recorded.
    NOTE: not compile-verified. -/
theorem logDensityLE_congr : ∀ A₁ B₁ A₂ B₂ : Set ℕ,
    LogDensityEquiv A₁ A₂ → LogDensityEquiv B₁ B₂ →
    HasLogDensityZero (A₁ \ B₁) = HasLogDensityZero (A₂ \ B₂) :=
  sorry

/-- The inclusion-modulo-ideal order on B₁: `[A] ≤ [B]` iff `A \ B` has
    natural density zero. This is the partial order of the quotient Boolean
    algebra; it replaces the input file's `BooleanAlgebra … := sorry`
    instance, whose data-level `sorry` left the order entirely unspecified
    (see the module docstring, encoding note 3). NOTE: not compile-verified. -/
instance : LE BoolAlgModNatDensity :=
  ⟨Quotient.lift₂ (fun A B => HasNaturalDensityZero (A \ B)) natDensityLE_congr⟩

/-- The inclusion-modulo-ideal order on B₂: `[A] ≤ [B]` iff `A \ B` has
    logarithmic density zero. See the B₁ instance above.
    NOTE: not compile-verified. -/
instance : LE BoolAlgModLogDensity :=
  ⟨Quotient.lift₂ (fun A B => HasLogDensityZero (A \ B)) logDensityLE_congr⟩

/--
Erdős Problem #1123 (Erdős–Ulam; INDEPENDENT of ZFC; \$100 prize):
Let B₁ be the Boolean algebra of sets of integers modulo sets of density 0
and let B₂ be the Boolean algebra of sets modulo sets of logarithmic density 0.
Prove that B₁ and B₂ are not isomorphic.

Encoded as: there is no order isomorphism between the two quotients, each
carrying its concrete inclusion-modulo-ideal order. For Boolean algebras an
order isomorphism is the same as a Boolean-algebra isomorphism, so this
faithfully encodes non-isomorphism (module docstring, encoding note 3).

This is independent of ZFC: Just and Krawczyk [JuKr84] proved under the
continuum hypothesis that these two algebras ARE isomorphic, while Farah
[Fa00, Corollary 3.4.4] proved under OCA + MA (consistent with ZFC by
[ARS85]) that they are NOT. The `sorry` records the problem statement as
posed by the source, not a provability claim.
-/
theorem erdos_problem_1123 :
    ¬ Nonempty (BoolAlgModNatDensity ≃o BoolAlgModLogDensity) :=
  sorry

/-- Two sets of naturals are equivalent modulo finite sets iff they agree
    from some point on (equivalently: their symmetric difference is finite).
    NOTE: added for the page-confirmed variants; not compile-verified. -/
def FinDiffEquiv (A B : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → (k ∈ A ↔ k ∈ B)

/-- The finite sets form an ideal, so `FinDiffEquiv` is an equivalence
    relation. A true proposition, `sorry`-recorded; not compile-verified. -/
theorem finDiffEquiv_equivalence : Equivalence FinDiffEquiv :=
  sorry

/-- The equivalence relation on Set ℕ given by finite symmetric difference. -/
def finDiffSetoid : Setoid (Set ℕ) where
  r := FinDiffEquiv
  iseqv := finDiffEquiv_equivalence

/-- The Boolean algebra of sets of integers modulo finite sets. -/
def BoolAlgModFinite : Type := Quotient finDiffSetoid

/-- Almost-inclusion (`A ⊆ B` from some point on, i.e. `A \ B` finite) is
    well defined on classes modulo finite sets. A true proposition,
    `sorry`-recorded; not compile-verified. -/
theorem finDiffLE_congr : ∀ A₁ B₁ A₂ B₂ : Set ℕ,
    FinDiffEquiv A₁ A₂ → FinDiffEquiv B₁ B₂ →
    (∃ N : ℕ, ∀ k : ℕ, N ≤ k → k ∈ A₁ → k ∈ B₁) =
    (∃ N : ℕ, ∀ k : ℕ, N ≤ k → k ∈ A₂ → k ∈ B₂) :=
  sorry

/-- The almost-inclusion order on the mod-finite quotient: `[A] ≤ [B]` iff
    `A \ B` is finite (encoded as: `A ⊆ B` from some point on).
    NOTE: not compile-verified. -/
instance : LE BoolAlgModFinite :=
  ⟨Quotient.lift₂ (fun A B => ∃ N : ℕ, ∀ k : ℕ, N ≤ k → k ∈ A → k ∈ B)
    finDiffLE_congr⟩

/-- Page-confirmed remark of Erdős and Ulam: the Boolean algebra of sets of
    integers modulo *finite* sets is not isomorphic to B₁ (nor to B₂ — see
    the next variant), "because the former has no upper bound while the
    other two do" (quoted verbatim from the source page). Stated on the page
    as a known fact. NOTE: added from the recovered source page; not
    compile-verified. -/
theorem erdos_problem_1123.variants.finite_vs_natDensity :
    ¬ Nonempty (BoolAlgModFinite ≃o BoolAlgModNatDensity) :=
  sorry

/-- Page-confirmed remark of Erdős and Ulam: the Boolean algebra of sets of
    integers modulo finite sets is not isomorphic to B₂. See
    `erdos_problem_1123.variants.finite_vs_natDensity`. NOTE: added from the
    recovered source page; not compile-verified. -/
theorem erdos_problem_1123.variants.finite_vs_logDensity :
    ¬ Nonempty (BoolAlgModFinite ≃o BoolAlgModLogDensity) :=
  sorry

end
