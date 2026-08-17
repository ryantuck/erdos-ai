import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Divisors

open Finset BigOperators

/--
The set of divisors of n strictly between 1 and n:
D(n) = { d ∈ ℕ | d ∣ n ∧ 1 < d ∧ d < n }
-/
def erdos45_divisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun d => 1 < d ∧ d < n)

/--
Erdős Problem #45 [Er95] [Er96b] — SOLVED (yes), proved by Croot [Cr03]
(erdosproblems.com/45, page last edited 28 September 2025, accessed 2026-02-22):

"Let k ≥ 2. Is there an integer n_k such that, if D = {1 < d < n_k : d ∣ n_k},
then for any k-colouring of D there is a monochromatic subset D' ⊆ D such that
∑_{d ∈ D'} 1/d = 1?"

The theorem below asserts the affirmative answer directly: for every k ≥ 2 there
exists n such that any k-colouring of the set D(n) of divisors of n (excluding 1
and n itself) admits a monochromatic subset D' whose reciprocals sum to 1.
(The docstring's "integer n" is `n : ℕ` here; this is equivalent, since no
n ≤ 2 can be a witness — `erdos45_divisors n = ∅` for such n, so no nonempty
D' exists.)

Status and provenance:
- Page banner at capture: PROVED, tooltip "This has been solved in the
  affirmative."
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a21, 2026-08-14) has superseding data: state "proved (Lean)"
  (informal status "proved", formal status "Lean", last update 2026-05-06);
  formalized statement: yes (2026-08-03); no prize.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/45.lean,
  HEAD 273e79a, 2026-08-16) encodes the same proposition in question form,
  `answer(True) ↔ ∀ k, 2 ≤ k → ∃ n, ...`, tagged `research solved` with a
  `formal_proof` attribute pointing at
  https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos45.lean
  — i.e. the affirmative resolution has itself been verified in Lean. The
  right-hand side there is the statement below (with the redundant
  `D'.Nonempty` conjunct dropped and the sum taken in ℝ via
  `Finset.reciprocalSum`; both encodings agree — see the review).

Remarks from the source page: "This follows from the colouring result of Croot
[Cr03]. Croot's result allows for n_k ≤ e^{C^k} for some constant C > 1 (simply
taking n_k to be the lowest common multiple of some interval [1, C^k]). Sawhney
has observed that there is also a doubly exponential lower bound, and hence
this bound is essentially sharp. Indeed, we must trivially have
∑_{d ∣ n_k} 1/d ≥ k, or else there is a greedy colouring as a counterexample.
Since ∏_p (1 + 1/p²) is finite we must have ∏_{p ∣ n_k} (1 + 1/p) ≫ k. To
achieve the minimal ∏_{p ∣ n_k} p we take the product of primes up to T where
∏_{p ≤ T} (1 + 1/p) ≫ k; by Mertens theorems this implies T ≥ C^k for some
constant C > 1, and hence n_k ≥ ∏_{p ∣ n_k} p ≥ exp(cC^k) for some c > 0. The
existence of such an n_k is mentioned in problem B2 of Guy's collection [Gu04]."

References (page citation line "#45: [Er95] [Er96b]"; [Cr03] and [Gu04] cited
in the remarks; no /latex/45 capture exists in the session logs, so entries
below come from the original pipeline's page-bib extraction and the upstream
formal-conjectures reference block, with provenance flagged):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Stub: upstream
  formal-conjectures 45.lean entry; note the archived deepmind corpus carries
  a conflicting expansion of this key — "Some of my favourite problems in
  various branches of combinatorics", Congressus Numerantium 107 (1995) — the
  upstream/site version is preferred here; volume number DEFERRED.)
- [Er96b] Erdős, P., _Some problems I presented or planned to present in my
  short talk_. Analytic number theory, Vol. 1 (Allerton Park, IL, 1995)
  (1996), 333-335. (Stub: upstream entry, agreeing with the deepmind corpus.)
- [Cr03] Croot, III, Ernest S., _On a coloring conjecture about unit
  fractions_. Ann. of Math. (2) (2003), 545-556. (Recovered from the original
  pipeline's page-bib extraction; agrees with upstream. The deepmind corpus
  supplies volume 157, consistent with reviewer knowledge, but the volume is
  absent from the recovered site data: DEFERRED.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. (2004), xviii+437.
  Problem B2. (Recovered from the page-bib extraction; "3rd ed., Springer"
  per the deepmind corpus.)

Tags: number theory | unit fractions | ramsey theory. No prize.
Related OEIS sequences: "Possible" (no specific sequence listed on the page).
Additional thanks to: Mehtaab Sawhney.
Source: https://www.erdosproblems.com/45
-/
theorem erdos_problem_45 :
    ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, ∀ (c : ℕ → Fin k),
        ∃ D' : Finset ℕ, D' ⊆ erdos45_divisors n ∧
          D'.Nonempty ∧
          (∃ j : Fin k, ∀ d ∈ D', c d = j) ∧
          (∑ d ∈ D', (1 : ℚ) / (d : ℚ)) = 1 :=
  sorry

/--
Quantitative upper bound, from the source page's remarks: "Croot's result
allows for n_k ≤ e^{C^k} for some constant C > 1 (simply taking n_k to be the
lowest common multiple of some interval [1, C^k])."

Encoded here with natural-number powers only (no `Real.exp` import needed):
there is a natural constant C ≥ 2 such that for every k ≥ 2 a witness
n ≤ C^(C^k) exists. This is equivalent to the page's bound up to the choice of
constant: e^{C₀^k} ≤ 3^{C₀^k} ≤ C₁^(C₁^k) for C₁ = max(3, ⌈C₀⌉), and
conversely C^(C^k) = e^{(ln C)·C^k} is again of the form e^{C'^k} for any
C' > C once k is large, with small k absorbed into the constant. By Sawhney's
doubly exponential lower bound (page remark, not separately formalized here —
the page states no precise constant/shape for it), this upper bound is
essentially sharp.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_45.variants.upper_bound :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ k : ℕ, k ≥ 2 →
      ∃ n : ℕ, n ≤ C ^ (C ^ k) ∧ ∀ (c : ℕ → Fin k),
        ∃ D' : Finset ℕ, D' ⊆ erdos45_divisors n ∧
          D'.Nonempty ∧
          (∃ j : Fin k, ∀ d ∈ D', c d = j) ∧
          (∑ d ∈ D', (1 : ℚ) / (d : ℚ)) = 1 :=
  sorry

/--
Necessary condition, from the source page's remarks: "we must trivially have
∑_{d ∣ n_k} 1/d ≥ k, or else there is a greedy colouring as a counterexample."

That is: if n is a valid witness for k (every k-colouring of D(n) admits a
monochromatic subset with reciprocal sum 1), then the reciprocal sum of *all*
divisors of n (including 1 and n, i.e. σ(n)/n) is at least k.

Reviewer verification of the page's greedy argument: if ∑_{d ∣ n} 1/d < k,
then ∑_{d ∈ D(n)} 1/d < k - 1 - 1/n. Colour each divisor d ∈ D(n) with
d ≤ k into its own class (there are at most k - 1 such d), then greedily place
the remaining divisors (each with 1/d < 1/k) into any of the k classes keeping
every class total < 1. If some item could not be placed, every class total
would exceed 1 - 1/k, forcing ∑_{d ∈ D(n)} 1/d > k(1 - 1/k) = k - 1, a
contradiction; so the greedy colouring succeeds and every monochromatic subset
sums to strictly less than 1. Hence no valid witness has ∑_{d ∣ n} 1/d < k.

For n with `erdos45_divisors n = ∅` (n ≤ 2) the hypothesis is unsatisfiable
(no nonempty D' exists), so the implication is vacuously true there, matching
the page's implicit restriction to genuine witnesses.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_45.variants.reciprocal_sum_necessary :
    ∀ k : ℕ, k ≥ 2 → ∀ n : ℕ,
      (∀ (c : ℕ → Fin k),
        ∃ D' : Finset ℕ, D' ⊆ erdos45_divisors n ∧
          D'.Nonempty ∧
          (∃ j : Fin k, ∀ d ∈ D', c d = j) ∧
          (∑ d ∈ D', (1 : ℚ) / (d : ℚ)) = 1) →
      (k : ℚ) ≤ ∑ d ∈ n.divisors, (1 : ℚ) / (d : ℚ) :=
  sorry
