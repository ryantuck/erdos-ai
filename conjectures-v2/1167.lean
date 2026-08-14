import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Finset.Basic

open Cardinal

noncomputable section

/-!
# Erdős Problem #1167

Let r ≥ 2 be finite and λ be an infinite cardinal. Let κ_α be cardinals for
all α < γ.

Is it true that 2^λ → (κ_α + 1)_{α < γ}^{r+1} implies λ → (κ_α)_{α < γ}^r?

Here + means cardinal addition, so κ_α + 1 = κ_α if κ_α is infinite.

A problem of Erdős, Hajnal, and Rado [Va99, 7.79].

Status: OPEN (erdosproblems.com/1167; tooltip "This is open, and cannot be
resolved with a finite computation"; page last edited 23 January 2026,
accessed 2026-02-23; the teorth/erdosproblems metadata mirror confirms state
"open", last update 2026-01-23, no prize, OEIS "N/A"). The page lists no
remarks, partial results, or related problems beyond the attribution line.
The page records 3 forum comments; their contents were not captured in the
archived logs. Page tags: set theory, ramsey theory. (The metadata mirror's
tag list reads ["set theory", "probability"]; "probability" appears to be a
database slip — the recovered page itself shows "set theory | ramsey theory",
which is what is recorded here.)

The question asks whether the (r+1)-exponent partition relation at 2^λ (with
each target raised by one) can be "stepped down" to the r-exponent relation
at λ — a converse-type companion to the classical Erdős–Rado stepping-up
direction, which passes from exponent r to exponent r + 1.

The source poses this as a yes/no question and the problem is OPEN; this raw
corpus has no `answer()` elaborator (Mathlib-only imports), and its uniform
convention for open yes/no questions is a direct assertion of the asked
("yes") direction with a `sorry` proof, as here: proving the theorem answers
the displayed question "yes", refuting it answers "no".

References (honest stub; no `/bibs/Va99` fetch was captured in the session
logs, so the entry carries only corpus-corroborated data — nothing
fabricated):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999, §7.79.
(Identification of this site-wide key recovered from the pipeline logs — the
upstream formal-conjectures contribution guide quotes exactly this entry as
its worked example — and corroborated by 20+ sibling problems in this corpus.
The section number 7.79 is from the recovered page's [Va99,7.79] citation
link. The "Vaughan, J., *Small uncountable cardinals and topology*" expansion
asserted by the archived prior review and styled file is unsupported by any
recovered source and is not carried here.)

Tags: set theory, ramsey theory
-/

/-- The cardinal partition relation κ → (targets α)_{α : ι}^r:
    for every coloring of the r-element subsets of a κ-sized set with colors from ι,
    there exists a color i and a monochromatic subset of cardinality ≥ targets i.

    Notes: quantifying over all types `S` with `#S = κ` is equivalent to fixing one
    representative, since the property is invariant under bijections and every
    cardinal is attained (`Quotient.out`). Coloring all of `Finset S` (with the
    homogeneity condition restricted to r-element subsets) is equivalent to coloring
    only the r-element subsets: when ι is nonempty any partial coloring extends, and
    when ι is empty both readings are vacuously true. Asking `#H ≥ targets i` rather
    than equality is also equivalent, since subsets of homogeneous sets are
    homogeneous. The `[DecidableEq S]` binder is classically satisfiable for every
    `S` and the body does not depend on the instance, so it does not restrict
    generality. -/
def CardinalPartitionRel (κ : Cardinal) {ι : Type*} (targets : ι → Cardinal) (r : ℕ) : Prop :=
  ∀ (S : Type*) [DecidableEq S] (_ : #S = κ) (c : Finset S → ι),
    ∃ (i : ι) (H : Set S),
      #H ≥ targets i ∧
      ∀ s : Finset S, s.card = r → (↑s : Set S) ⊆ H → c s = i

/-- **Erdős Problem #1167** (Erdős–Hajnal–Rado) [Va99, 7.79]:
    For r ≥ 2 and λ infinite, does 2^λ → (κ_α + 1)^{r+1} imply λ → (κ_α)^r?

    The problem is OPEN; per this corpus's convention for open yes/no questions the
    asked ("yes") direction is stated directly, with the color family indexed by an
    arbitrary type ι in place of the source's ordinal-indexed family (κ_α)_{α<γ} —
    an equivalent, standard generalization, with the same index type in hypothesis
    and conclusion as in the source. -/
theorem erdos_conjecture_1167
    {ι : Type*} (κ : ι → Cardinal) (lam : Cardinal) (r : ℕ)
    (hr : r ≥ 2) (hlam : ℵ₀ ≤ lam) :
    CardinalPartitionRel ((2 : Cardinal) ^ lam) (fun α => κ α + 1) (r + 1) →
    CardinalPartitionRel lam κ r :=
  sorry

end
