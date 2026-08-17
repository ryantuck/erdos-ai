import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem 90: the unit distance problem

*Reference:* [erdosproblems.com/90](https://www.erdosproblems.com/90)

Does every set of $n$ distinct points in $\mathbb{R}^2$ contain at most
$n^{1+O(1/\log\log n)}$ many pairs which are distance 1 apart?

**Status: DISPROVED (May 2026) — the answer is NO.** The conjecture, dating to 1946
[Er46b] and carrying a \$500 prize, was refuted by a construction found by an internal
model at OpenAI, digested and human-verified in two 2026 arXiv papers:

* W. Sawin, *An explicit lower bound for the unit distance problem*,
  arXiv:2605.20579 (2026): $u(n) \ge n^{1.014114}/C$ for infinitely many $n$;
* N. Alon, T. F. Bloom, W. T. Gowers, D. Litt, W. Sawin, A. Shankar, J. Tsimerman,
  V. Wang, and M. Matchett Wood, *Remarks on the disproof of the unit distance
  conjecture*, arXiv:2605.20695 (2026): qualitative form $u(n) \ge n^{1+\varepsilon}$
  for some absolute $\varepsilon > 0$ and infinitely many $n$.

(Status provenance: `teorth/erdosproblems` `data/problems.yaml`, status
"disproved (Lean)", last update 2026-06-07, and the upstream
`google-deepmind/formal-conjectures` file for problem 90 at its August 2026 HEAD,
which states `answer(False)`. The archived erdosproblems.com/90 page recovered from the
pipeline logs — accessed 2026-03-05, last edited 23 January 2026 — predates the
resolution and still shows OPEN.)

Background (from the archived page): Erdős dates the conjecture to 1946 in [Er94b];
in [Er82e] he offered \$300, and in [Er83c] and [Er85] \$250, for the upper bound
$n^{1+o(1)}$. A $\sqrt{n}\times\sqrt{n}$ section of the integer lattice attains
$n^{1+c/\log\log n}$ unit distances [Er46b], which had been conjectured best possible.
It is easy to show $O(n^{3/2})$; the best known upper bound is $O(n^{4/3})$, due to
Spencer, Szemerédi, and Trotter [SST84]. Valtr (see [Sz16]) constructed a metric on
$\mathbb{R}^2$ and $n$ points with $\gg n^{4/3}$ unit-distance pairs for that metric,
and the [SST84] proof generalises to it, so beating $n^{4/3}$ must exploit a special
feature of the Euclidean metric. See the survey [Sz16].

Cross-references: erdosproblems.com problems [92], [96], [605], [956]; the higher
dimensional generalisation is [1085]. Related OEIS sequence: A186705.

References (recovered provenance noted; entries without full data are honest stubs —
the site's `/bibs` data was not captured in the logs):

* [Er46b] Erdős, P., *On sets of distances of $n$ points*. Amer. Math. Monthly (1946),
  248–250. (Bibliographic data from sibling files in this repo carrying the same key.)
* [Er61] Erdős, P., *Some unsolved problems*. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961). (Sibling-file stub.)
* [Er75f] Erdős, P., *On some problems of elementary and combinatorial geometry*.
  Annali di Matematica Pura ed Applicata (1975), 99–108. Cited at p. 100.
  (Sibling-file stub, consistent with the page's `[Er75f,p.100]` pointer.)
* [Er81], [Er82e], [Er83c], [Er85], [Er90], [Er94b], [Er95], [Er97c], [Er97e],
  [Er97f] Erdős, P. — problem-survey papers; full data DEFERRED (not recoverable
  offline).
* [Va99] Various, *Some of Paul's favorite problems*. Booklet produced for the
  conference "Paul Erdős and his mathematics" (1999). Cited at 4.67.
  (Sibling-file stub.)
* [SST84] Spencer, J., Szemerédi, E., and Trotter, W. T., 1984. (Full data DEFERRED.)
* [Sz16] Szemerédi, E., survey, 2016. (Full data DEFERRED.)
-/

open Real Finset

noncomputable section

/--
The number of unit-distance pairs in a finite point set in ℝ²:
the number of ordered pairs (p, q) with p ≠ q and dist(p, q) = 1.
We count ordered pairs, which is exactly twice the number of unordered pairs.
For the asymptotic bounds below (with card ≥ 3, where log log card > 0) the factor
of 2 is absorbed by the constants, so ordered counting is harmless; note that at
card = 2 this absorption fails, which is one reason the statements below avoid
cardinality 2.
-/
def unitDistancePairs (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card

/--
Erdős Problem #90 [Er46b, Er61, Er75f, Er81, Er82e, Er83c, Er85, Er90, Er94b,
Er95, Er97c, Er97e, Er97f, Va99]:

Does every set of n distinct points in ℝ² contain at most n^{1+O(1/log log n)}
many pairs which are distance 1 apart?

**The answer is NO** (disproved May 2026; Sawin, arXiv:2605.20579, and
Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood,
arXiv:2605.20695): there is an absolute constant c > 0 such that infinitely many n
admit n-point configurations with at least n^{1+c} unit distances, while
n^{1+C/log log n} = n^{1+o(1)} for every fixed C. We therefore assert the
*negation* of the conjectured bound.

Encoding notes:
* "at most n^{1+O(1/log log n)}" is rendered as "∃ C > 0 uniform over all
  configurations of at least 3 points". For card ≥ 3 we have log log card > 0, so
  enlarging C only weakens the bound and the finitely many small cardinalities are
  absorbed; this makes the inner statement equivalent to the eventual (all
  sufficiently large n) form, and its negation equivalent to the disproof.
* The threshold is 3, not 2: at card = 2 we have log(log 2) < 0, so the bound
  2^{1+C/log log 2} < 2 fails for two points at unit distance for *every* C > 0,
  and the negation would be trivially true for a spurious reason. (The original
  first-pass file used `2 ≤ A.card`, making its positive statement literally false
  even before the disproof.)
* `unitDistancePairs` counts ordered pairs (twice the unordered count); for card ≥ 3
  the factor 2 is absorbed into C, so the inner ∃-statement is equivalent to the
  unordered form.

Not compile-verified: this statement was revised during review without a Lean
toolchain available.
-/
theorem erdos_problem_90 :
    ¬ ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        3 ≤ A.card →
        (unitDistancePairs A : ℝ) ≤
          (A.card : ℝ) ^ (1 + C / Real.log (Real.log (A.card : ℝ))) :=
  sorry

/--
Erdős's lattice lower bound [Er46b]: a √n × √n section of the integer lattice shows
that there exist n-point configurations with at least n^{1+c/log log n} unit-distance
pairs, for some absolute constant c > 0 and arbitrarily large n. This is why the
conjectured upper bound, if true, would have been best possible. (Lower bounds
transfer verbatim to the ordered count, which is at least the unordered count.)

Not compile-verified.
-/
theorem erdos_problem_90.variants.lattice_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card ∧ 3 ≤ A.card ∧
        (A.card : ℝ) ^ (1 + c / Real.log (Real.log (A.card : ℝ))) ≤
          (unitDistancePairs A : ℝ) :=
  sorry

/--
The Spencer–Szemerédi–Trotter upper bound [SST84]: every finite point set in ℝ²
determines O(n^{4/3}) unit distances. This remains the best known upper bound.
(The ordered count is twice the unordered one; the factor 2 is absorbed into C.)

Not compile-verified.
-/
theorem erdos_problem_90.variants.sst_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        (unitDistancePairs A : ℝ) ≤ C * (A.card : ℝ) ^ ((4 : ℝ) / 3) :=
  sorry

/--
Qualitative form of the 2026 disproof (Theorem 1.1 of
Alon–Bloom–Gowers–Litt–Sawin–Shankar–Tsimerman–Wang–Matchett Wood,
arXiv:2605.20695): there is an absolute constant c > 0 such that arbitrarily large
(equivalently, infinitely many) n admit n-point configurations with at least
n^{1+c} unit-distance pairs. This refutes the conjectured n^{1+O(1/log log n)}
upper bound. (A lower bound on the unordered count transfers verbatim to the
ordered count.)

Not compile-verified.
-/
theorem erdos_problem_90.variants.polynomial_lower_bound :
    ∃ c : ℝ, 0 < c ∧
      ∀ N : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card ∧ (A.card : ℝ) ^ (1 + c) ≤ (unitDistancePairs A : ℝ) :=
  sorry

/--
Sawin's explicit form of the disproof (Theorem 1 of Sawin, arXiv:2605.20579, as
quoted by the upstream formal-conjectures file): there is a constant C > 0 such
that infinitely many n admit n-point configurations with at least n^{1.014114}/C
unit-distance pairs. We keep Sawin's implicit constant C rather than absorbing it
into the exponent (the upstream file states the constant-free form
u(n) ≥ n^{1.014114} infinitely often, which is formally stronger; the form below
is the conservative reading of the theorem as quoted).

Not compile-verified.
-/
theorem erdos_problem_90.variants.sawin_explicit_lower_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card ∧
        (A.card : ℝ) ^ (1.014114 : ℝ) / C ≤ (unitDistancePairs A : ℝ) :=
  sorry

end
