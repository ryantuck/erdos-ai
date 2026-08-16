import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem 33

*Reference:* [erdosproblems.com/33](https://www.erdosproblems.com/33)
(accessed 2026-03-05, page edition 27 December 2025; page content recovered from an
archived session-log capture — the live site is unreachable from the review container).

Statement (verbatim from the site): "Let $A\subset\mathbb{N}$ be such that every large
integer can be written as $n^2+a$ for some $a\in A$ and $n\geq 0$. What is the smallest
possible value of \[\limsup \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N^{1/2}}?\] Is
\[\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N^{1/2}}>1?\]" [Er56, p.134]

Status: **OPEN** ("This is open, and cannot be resolved with a finite computation").
The teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit
a09c7a21, 2026-08-14) agrees: status "open" (last update 2025-08-31); tags: number
theory, additive basis; no OEIS references; no prize.

Remarks from the page: such a set $A$ is called an *additive complement* of the set of
squares. Erdős observed that there exist $A$ for which the $\limsup$ is finite and
$>1$. Moser [Mo65] proved that, for any such $A$,
$\liminf \lvert A\cap\{1,\ldots,N\}\rvert/N^{1/2} > 1.06$ — so the liminf question as
literally asked ("is it $>1$?") is answered affirmatively, and the open content is
quantitative. The best-known lower bound is
$\liminf \geq 4/\pi \approx 1.273$, proved by Cilleruelo [Ci93], Habsieger [Ha95], and
Balasubramanian–Ramana [BaRa01]. The problem of minimising the $\limsup$ appears to
have been much less studied; van Doorn has a construction of such an $A$ with
$\lvert A\cap\{1,\ldots,N\}\rvert/N^{1/2} < 2\varphi^{5/2} \approx 6.66$ for all $N$,
where $\varphi = (1+\sqrt{5})/2$ is the golden ratio.

The "smallest possible value of the limsup" part is a value request about an open
quantity; without the styled `answer()` machinery (not part of this raw pipeline) it is
represented here by the finiteness statement `erdos_problem_33_limsup_finite` and the
van Doorn upper-bound variant, with the infimum question left open and noted here.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Mo65] Moser, L. (Bibliographic stub: the recovered page shows only the key and the
attribution "Moser"; no `/latex/33` fetch exists in the session logs, so journal data
is not recoverable offline and is not fabricated here.)

[Ci93] Cilleruelo, J. (Stub; as for [Mo65].)

[Ha95] Habsieger, L. (Stub; as for [Mo65].)

[BaRa01] Balasubramanian, R. and Ramana, D. S. (Stub; as for [Mo65].)

Bibliographic provenance: [Er56] full entry from the upstream
google-deepmind/formal-conjectures repository (commit dd1c2beb, e.g.
`FormalConjectures/ErdosProblems/1.lean` and `31.lean`); the other four keys appear on
the recovered page only as citation links with author surnames in the prose, so they
are recorded as honest stubs.
-/

open Classical

/--
A set A ⊆ ℕ is an additive complement of the squares if every sufficiently large
natural number can be written as n² + a for some n ≥ 0 and a ∈ A.
-/
def IsAdditiveComplementOfSquares (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ m : ℕ, N₀ ≤ m → ∃ n : ℕ, ∃ a ∈ A, m = n ^ 2 + a

/--
The counting function |A ∩ {1, …, N}| / N^{1/2} for a set A ⊆ ℕ.
-/
noncomputable def sqrtNormalizedCount (A : Set ℕ) (N : ℕ) : ℝ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ^ ((1 : ℝ) / 2)

/--
Erdős Problem #33 [Er56, p.134] (liminf part):

Let A ⊆ ℕ be such that every large integer can be written as n² + a for some
a ∈ A and n ≥ 0 (i.e., A is an additive complement of the squares). Then
liminf |A ∩ {1,…,N}| / N^{1/2} > 1.

Erdős asked this as a question ("Is liminf > 1?"); it was answered affirmatively by
Moser [Mo65] (liminf > 1.06), and the best-known lower bound is liminf ≥ 4/π ≈ 1.273,
proved by Cilleruelo [Ci93], Habsieger [Ha95], and Balasubramanian–Ramana [BaRa01].
The direct-assertion form below therefore states the true (proved) direction.

Encoding note ([defect] fix, not compile-verified): the input file stated
`1 < Filter.liminf (fun N => sqrtNormalizedCount A N) Filter.atTop` with values in ℝ.
Mathlib's ℝ-valued `Filter.liminf` unfolds to `sSup {c | ∀ᶠ N in atTop, c ≤ f N}`,
and `Real.sSup` returns the junk value 0 on sets that are not bounded above
(`Real.sSup_of_not_bddAbove`). For `A = Set.univ` — which satisfies
`IsAdditiveComplementOfSquares` via `m = 0 ^ 2 + m` — the quotient is `√N → ∞`, the
set above is all of ℝ, and the Lean liminf evaluates to 0, making the original
statement `1 < 0` false for that A; the universally quantified theorem was therefore
provably false as written. The junk-free encoding below says precisely
"liminf > 1 in the extended-real sense": some real c > 1 is an eventual lower bound.
-/
theorem erdos_problem_33_liminf :
    ∀ A : Set ℕ, IsAdditiveComplementOfSquares A →
      ∃ c : ℝ, 1 < c ∧ ∀ᶠ N in Filter.atTop, c ≤ sqrtNormalizedCount A N :=
  sorry

/--
Erdős Problem #33 (Part 1, existence): There exists an additive complement of the
squares whose normalized counting function is uniformly bounded — equivalently, whose
limsup is finite (each value is a finite real and only finitely many indices lie below
any threshold, so eventual boundedness and global boundedness coincide here). Erdős
observed this; van Doorn's construction (see
`erdos_problem_33.variants.van_doorn`) gives an explicit bound `2φ^(5/2) ≈ 6.66`.
The page's actual Part 1 question — the smallest possible value of the limsup — is an
open value request, recorded in the module docstring and not expressible as a bare
proposition in this raw pipeline.
-/
theorem erdos_problem_33_limsup_finite :
    ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧
      ∃ C : ℝ, ∀ N : ℕ, 0 < N → sqrtNormalizedCount A N ≤ C :=
  sorry

/--
Moser's theorem [Mo65] (page-confirmed variant, not compile-verified): for any
additive complement A of the squares,
liminf |A ∩ {1,…,N}| / N^{1/2} > 1.06.
Junk-free encoding as in `erdos_problem_33_liminf`: some real c > 1.06 is an eventual
lower bound.
-/
theorem erdos_problem_33.variants.moser :
    ∀ A : Set ℕ, IsAdditiveComplementOfSquares A →
      ∃ c : ℝ, 1.06 < c ∧ ∀ᶠ N in Filter.atTop, c ≤ sqrtNormalizedCount A N :=
  sorry

/--
The best-known lower bound (page-confirmed variant, not compile-verified), proved by
Cilleruelo [Ci93], Habsieger [Ha95], and Balasubramanian–Ramana [BaRa01]: for any
additive complement A of the squares,
liminf |A ∩ {1,…,N}| / N^{1/2} ≥ 4/π ≈ 1.273.
Junk-free encoding of "liminf ≥ 4/π": every real c < 4/π is an eventual lower bound.
(`Real.pi` is transitively available from the
`Mathlib.Analysis.SpecialFunctions.Pow.Real` import.)
-/
theorem erdos_problem_33.variants.best_lower_bound :
    ∀ A : Set ℕ, IsAdditiveComplementOfSquares A →
      ∀ c : ℝ, c < 4 / Real.pi →
        ∀ᶠ N in Filter.atTop, c ≤ sqrtNormalizedCount A N :=
  sorry

/--
van Doorn's construction (page-confirmed variant, not compile-verified): there is an
additive complement A of the squares with
|A ∩ {1,…,N}| / N^{1/2} < 2φ^{5/2} ≈ 6.66 for all N,
where φ = (1 + √5)/2 is the golden ratio, written below via `rpow` (the only power
operation already used in this file: `√5 = (5 : ℝ) ^ ((1 : ℝ)/2)`). At `N = 0` the
quotient is 0 by Lean's division-by-zero convention, so the "for all N" form is
literally true for the constructed A.
-/
theorem erdos_problem_33.variants.van_doorn :
    ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧ ∀ N : ℕ,
      sqrtNormalizedCount A N <
        2 * ((1 + (5 : ℝ) ^ ((1 : ℝ) / 2)) / 2) ^ ((5 : ℝ) / 2) :=
  sorry
