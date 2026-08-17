import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem 32

*Reference:* [erdosproblems.com/32](https://www.erdosproblems.com/32)
(page edition 23 January 2026, accessed 2026-03-05; content recovered from the original
pipeline's capture of the then-extant `tidy/32.html`, preserved in the session logs —
the live site is unreachable from the review container).

Statement (verbatim from the site): "Is there a set $A\subset\mathbb{N}$ such that
$\lvert A\cap\{1,\ldots,N\}\rvert = o((\log N)^2)$ and such that every large integer can
be written as $p+a$ for some prime $p$ and $a\in A$?

Can the bound $O(\log N)$ be achieved? Must such an $A$ satisfy
$\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{\log N} > 1$?"

Such a set is called an *additive complement to the primes*.

Status: the site's banner is **OPEN** ("This is open, and cannot be resolved with a
finite computation."), displayed with a \$50 prize; problem E1 of Guy's collection
[Gu04] states that Erdős offered \$50 for determining whether $O(\log N)$ can be
achieved. The teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked
2026-08-16) agrees the problem is open (last update 2025-08-31), though its `prize`
field currently reads "no" — a discrepancy with the page capture, recorded here and not
resolved. Tags: number theory, additive basis; no OEIS references. The upstream
formal-conjectures repository formalizes this problem at
`FormalConjectures/ErdosProblems/32.lean` (all three questions, via `answer(sorry) ↔`
for the open parts and `EReal` liminf for the third).

Known results (site remarks):

* Erdős [Er54] proved that such a set $A$ exists with
  $\lvert A\cap\{1,\ldots,N\}\rvert\ll (\log N)^2$, improving a previous result of
  Lorentz [Lo54], who achieved $\ll(\log N)^3$. (First question: whether $o((\log N)^2)$
  is possible — open.)
* Wolke [Wo96] showed $\ll(\log N)^{1+o(1)}$ is achievable if we only ask for almost all
  integers to be representable; Kolountzakis [Ko96] improved this to
  $\ll(\log N)(\log\log N)$, and Ruzsa [Ru98c] further to $\ll\omega(N)\log N$ for any
  $\omega\to\infty$. (Not formalized here: would require an "almost all integers
  representable" density definition not present in this file — optional enrichment,
  deferred.)
* The answer to the third question is yes: Ruzsa [Ru98c] showed that every additive
  complement to the primes must satisfy
  $\liminf \lvert A\cap\{1,\ldots,N\}\rvert/\log N \geq e^\gamma \approx 1.781$.
  (The question as asked, with the weaker bound $>1$, is `erdos_problem_32c` below; the
  explicit $e^\gamma$ strengthening would need `Real.eulerMascheroniConstant` and hence
  a new import, so it is documented here but not formalized — deferred.)

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er57] Erdős, Paul, _Some unsolved problems_. Michigan Math. J. (1957), 291-300.

[Er59] Erdős, P., _Über einige Probleme der additiven Zahlentheorie_. Sammelband zu
Ehren des 250. Geburtstages Leonhard Eulers (1959), 116-119.

[Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
(1961), 221-254.

[Er65b] Erdős, Paul, _Some recent advances and current problems in number theory_.
Lectures on Modern Mathematics, Vol. III (1965), 196-244.

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138.

[Er77c] Erdős, Paul, _Problems and results on combinatorial number theory. III_. Number
theory day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43-72.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999). (The page cites this
problem as [Va99, 1.9]. A conflicting upstream entry "Vardi, I., Prime census. (1999)"
exists for the same key in one file; the booklet reading matches the site's
problem-number citation style. Partially DEFERRED.)

[Er54] Erdős, Paul, _Some results on additive number theory_. Proc. Amer. Math. Soc.
(1954), 847-853.

[Lo54] Lorentz, G. G., _On a problem of additive number theory_. Proc. Amer. Math. Soc.
(1954), 838-841. (Volume number absent from all recovered sources; not fabricated.)

[Wo96] Wolke — cited on the page for the $(\log N)^{1+o(1)}$ almost-all result. No
bibliographic details recoverable from the logs or the upstream repository: DEFERRED
(honest stub).

[Ko96] Kolountzakis — cited on the page for the $(\log N)(\log\log N)$ almost-all
result. No bibliographic details recoverable: DEFERRED (honest stub).

[Ru98c] Ruzsa, Imre Z., _On the additive completion of primes_. Acta Arith. (1998),
269-275.

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), xviii+437.
(Problem E1 discusses this problem.)

Bibliographic provenance: the page capture displays only the citation keys. [Er54],
[Ru98c], [Gu04] entries are from the upstream google-deepmind/formal-conjectures file
`FormalConjectures/ErdosProblems/32.lean` (commit dd1c2beb; the upstream key for [Er54]
is `[Erd54]`). [Er56], [Er57], [Er59], [Er61], [Er65b], [Er73], [Er77c], [Va99] are
from sibling upstream ErdosProblems files carrying the same keys. [Lo54] is from the
original pipeline's `/latex/31` fetch preserved in the session logs (problem 31 shares
the key). No `/latex/32` fetch survives in the logs; journal volume numbers are absent
throughout and remain DEFERRED.
-/

open Real Set

/--
A set A ⊆ ℕ is an **additive complement to the primes** if every sufficiently
large natural number can be written as p + a for some prime p and some a ∈ A.
-/
def IsAdditiveComplement (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ p : ℕ, Nat.Prime p ∧ ∃ a ∈ A, n = p + a

/--
The counting function of A up to N: |A ∩ {1, …, N}|.
-/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Icc 1 N).ncard

/--
Erdős Problem #32, first part [Er56, Er57, Er59, Er61, Er65b, Er73, Er77c, Va99]:

Is there a set A ⊂ ℕ such that |A ∩ {1,…,N}| = o((log N)²) and every
sufficiently large integer can be written as p + a for some prime p and a ∈ A?

Erdős [Er54] proved that such a set exists with |A ∩ {1,…,N}| ≪ (log N)²
(see `erdos_problem_32.variants.erdos_log_squared`).
The question is whether the (log N)² bound can be improved. **OPEN**; this raw pipeline
has no `answer()` elaborator, so per corpus convention the affirmative direction of the
question as asked is stated as a direct assertion (the upstream encoding is
`answer(sorry) ↔` this proposition).
-/
theorem erdos_problem_32a :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countingFn A N : ℝ) ≤ ε * (log N) ^ 2 :=
  sorry

/--
Erdős Problem #32, second part:

Can one find an additive complement A to the primes with
|A ∩ {1,…,N}| = O(log N)?

Per problem E1 of Guy's collection [Gu04], Erdős offered $50 for determining whether
this is possible. **OPEN**; affirmative direction stated as a direct assertion (corpus
convention, upstream `answer(sorry) ↔`).

Encoding note: the O-bound is stated eventually (`∃ N₀`) to match the asymptotic
$O(\log N)$; the input file's `∀ N ≥ 1` form was equivalent in truth value (shift the
witness set by 2) but forced the artificial boundary constraint `1 ∉ A` via
`log 1 = 0`.
-/
theorem erdos_problem_32b :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countingFn A N : ℝ) ≤ C * log N :=
  sorry

/--
Erdős Problem #32, third part:

Must every additive complement A to the primes satisfy
liminf_{N→∞} |A ∩ {1,…,N}| / log N > 1?

**SOLVED (yes)**: Ruzsa [Ru98c] proved that every additive complement to the primes
satisfies liminf |A ∩ {1,…,N}| / log N ≥ e^γ ≈ 1.781 > 1. The direct-assertion form
below states the proved direction of the question as asked (with the bound > 1; the
explicit e^γ strengthening is documented in the module docstring, deferred).

Encoding note: `liminf f N > 1` is rendered junk-value-free as
`∃ c > 1, ∀ large N, c * log N ≤ |A ∩ {1,…,N}|`. For real sequences this is equivalent
to the liminf statement — including when the ratio tends to infinity, where a literal
`Filter.liminf` over ℝ would collapse to the `Real.sSup` junk value 0 and make the
statement falsely false.
-/
theorem erdos_problem_32c :
    ∀ A : Set ℕ, IsAdditiveComplement A →
      ∃ c : ℝ, 1 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        c * log N ≤ (countingFn A N : ℝ) :=
  sorry

/--
Erdős [Er54] proved that an additive complement to the primes exists with
|A ∩ {1,…,N}| ≪ (log N)², improving a previous result of Lorentz [Lo54], who achieved
≪ (log N)³. This is the solved upper bound accompanying the open question
`erdos_problem_32a`. **SOLVED** (page-confirmed remark).
-/
theorem erdos_problem_32.variants.erdos_log_squared :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (countingFn A N : ℝ) ≤ C * (log N) ^ 2 :=
  sorry
