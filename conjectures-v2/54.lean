import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Basic

open Finset Real

attribute [local instance] Classical.propDecidable

/-!
# Erdős Problem #54

Verbatim statement from the source page (erdosproblems.com/54, page last
edited 28 October 2025, accessed 2026-02-22):

"A set of integers $A$ is Ramsey $2$-complete if, whenever $A$ is
$2$-coloured, all sufficiently large integers can be written as a
monochromatic sum of elements of $A$.

Burr and Erdős [BuEr85] showed that there exists a constant $c>0$ such that
it cannot be true that
$$\lvert A\cap \{1,\ldots,N\}\rvert \leq c(\log N)^2$$
for all large $N$ and that there exists a Ramsey $2$-complete $A$ such that
for all large $N$
$$\lvert A\cap \{1,\ldots,N\}\rvert < (2\log_2 N)^3.$$
Improve either of these bounds."

Status and provenance:
- Page banner at capture: **SOLVED**, tooltip "This has been resolved in some
  other way than a proof or disproof.", **$100 prize**.
- Remarks on the page: "The stated bounds are due to Burr and Erdős [BuEr85].
  Resolved by Conlon, Fox, and Pham [CFP21], who constructed a Ramsey
  $2$-complete $A$ such that $\lvert A\cap \{1,\ldots,N\}\rvert \ll
  (\log N)^2$ for all large $N$." The CFP21 upper bound matches the order of
  the Burr–Erdős lower bound, so the minimal possible growth of a Ramsey
  $2$-complete set is $\Theta((\log N)^2)$.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  entry `number: "54"`, clone at commit a09c7a2, 2026-08-14) agrees: state
  "solved" (last update 2025-08-31), prize $100, formalized "no",
  tags [number theory, ramsey theory], OEIS N/A.
- The upstream formal-conjectures repo has no `ErdosProblems/54.lean` at
  HEAD dd1c2beb (2026-08-16), consistent with the mirror and with the page's
  "Formalised statement? No" at capture.
- Cross-references on the page: see also Erdős problems [55] (the general
  Ramsey $r$-complete version, same authors and resolution) and [843]
  (a Ramsey-completeness variant, also resolved by [CFP21]).

References (entries marked "latex/54" are recovered from the original
pipeline's WebFetch extraction of erdosproblems.com/latex/54 preserved in the
session logs; volume numbers were not preserved by that extraction and remain
DEFERRED — nothing here is fabricated):
- [BuEr85] Burr, S. A. and Erdős, P., _A Ramsey-type property in additive
  number theory_. Glasgow Math. J. (1985), 5–10. (latex/54; volume number
  DEFERRED.)
- [CFP21] Conlon, D., Fox, J., and Pham, H. T., _Subset sums, completeness
  and colorings_. arXiv:2104.14766 (2021). (latex/54.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165–186. This problem:
  p. 172. (Not part of the /latex/54 bibliography — it is the problem-source
  key on the page ("#54: [Er95, p.172]"); the expansion is an honest stub
  from sibling corpus files (e.g. the archived styled artifact for this
  problem); unverified offline: DEFERRED.)

Site citation line: T. F. Bloom, Erdős Problem #54,
https://www.erdosproblems.com/54, accessed 2026-02-22.

Tags: number theory, ramsey theory
-/

/--
A set A of natural numbers is Ramsey 2-complete if for every 2-coloring of ℕ,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of A that all receive the same color.

Encoding notes (review pass):
- The source colours $A$ itself ("whenever $A$ is $2$-coloured"); colouring
  all of ℕ is equivalent under the universal quantifier over colourings,
  since every colouring of $A$ extends to ℕ and every colouring of ℕ
  restricts to $A$.
- "Monochromatic sum of elements of $A$" is encoded as a subset sum: a
  `Finset ℕ` of distinct elements of $A$, all of one colour, summing to $n$.
  This is the standard (Burr–Erdős) notion of completeness by sums of
  distinct terms.
- The threshold `N₀` may depend on the colouring `χ`, exactly as in the
  source, where "all sufficiently large" sits inside the scope of "whenever
  $A$ is $2$-coloured".
- Degenerate inputs: the empty `Finset` represents only $n = 0$, which is
  immaterial under "all sufficiently large"; membership of $0$ in $A$ is
  likewise immaterial (removing $0$ from a witness `S` changes neither its
  sum nor its monochromaticity).
-/
def IsRamsey2Complete (A : Set ℕ) : Prop :=
  ∀ (χ : ℕ → Fin 2),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin 2, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem #54 (SOLVED; resolved by Conlon, Fox, and Pham [CFP21]):
There exists a Ramsey 2-complete set A ⊆ ℕ and a constant c > 0
such that |A ∩ {1,...,N}| ≤ c · (log N)² for all sufficiently large N.

This improves the upper bound (2 log₂ N)³ of Burr and Erdős [BuEr85],
matching the order of their lower bound (see
`erdos_problem_54.variants.lower_bound`), so the minimal growth is
$\Theta((\log N)^2)$.

Polarity note (review pass): the problem as posed asks to "improve either of
these bounds"; this direct assertion is the statement that [CFP21] proved,
i.e. the true direction of the resolution. The base of the logarithm is
immaterial (it is absorbed into $c$); the source's "set of integers" is
`Set ℕ` here, as only positive elements can contribute to sums of distinct
positive integers and only $\{1,\ldots,N\}$ is counted.
-/
theorem erdos_problem_54 :
    ∃ (A : Set ℕ),
      IsRamsey2Complete A ∧
        ∃ c : ℝ, c > 0 ∧
          ∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (Real.log (N : ℝ)) ^ 2 :=
  sorry

/--
Burr–Erdős lower bound [BuEr85], stated verbatim on the source page: there
exists a constant $c > 0$ such that it cannot be true, for a Ramsey
$2$-complete $A$, that $|A \cap \{1,\ldots,N\}| \leq c (\log N)^2$ for all
large $N$. Contrapositively (as encoded here): any $A$ satisfying that bound
for all sufficiently large $N$ fails to be Ramsey $2$-complete. Together with
`erdos_problem_54` this pins the minimal possible growth at
$\Theta((\log N)^2)$ — the content of the full resolution of the problem.

Page-confirmed variant added by the review pass (Fable, 2026-08-16), using
only constructs already present in this file; not compile-verified.
-/
theorem erdos_problem_54.variants.lower_bound :
    ∃ c : ℝ, c > 0 ∧
      ∀ (A : Set ℕ),
        (∃ N₀ : ℕ, ∀ N ≥ N₀,
          (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
            c * (Real.log (N : ℝ)) ^ 2) →
        ¬ IsRamsey2Complete A :=
  sorry
