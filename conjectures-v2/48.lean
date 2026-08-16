import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors

open Finset Nat

/--
The sum of divisors function σ(n) = Σ_{d | n} d.

Note (Fable review): this equals Mathlib's `Nat.sigma 1 n` (available from the
`Mathlib.NumberTheory.Divisors` import already present; the upstream
formal-conjectures file writes it `σ 1 m` under `open scoped
ArithmeticFunction.sigma`). The local definition is kept because swapping it is
a compiler-dependent change. On the degenerate input: `Nat.divisors 0 = ∅`, so
`sumDivisors 0 = 0` — harmless here, since the theorem below guards `0 < m`.
-/
def sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/--
Erdős Problem #48 [Er59c] [Er74b] [ErGr80] [Er95] — PROVED
(erdosproblems.com/48, page last edited 17 October 2025, accessed 2026-03-05):

"Are there infinitely many integers n, m such that φ(n) = σ(m)?"

This would follow immediately from the twin prime conjecture (for twin primes
p, p+2 one has σ(p) = p + 1 = φ(p+2)). The answer is yes, proved
unconditionally by Ford, Luca, and Pomerance [FLP10], who in fact prove there
are at least exp((log log x)^c) many a ≤ x such that a = φ(n) = σ(m) for some
n, m, where c > 0 is an absolute constant. This lower bound was improved to
exp((log log x)^{ω(x)}) for some ω(x) → ∞ by Garaev [Ga11].

This is problem B38 of Guy's collection [Gu04].

Status and provenance:
- Page banner at capture: PROVED, tooltip "This has been solved in the
  affirmative."
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "proved", last update 2025-08-31;
  no prize; OEIS: N/A; formalized: yes (2025-08-31); tags: number theory.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/48.lean,
  HEAD dd1c2beb, 2026-08-16) marks `erdos_48` as `research solved` and states
  `answer(True) ↔ {(n, m) : ℕ × ℕ | n.totient = σ 1 m}.Infinite`.
- The direct assertion below is the proved affirmative direction of the page's
  yes/no question, per this corpus's convention for solved problems.

Encoding notes:
- "Infinitely many n" is encoded as unboundedness (`∀ N, ∃ n ≥ N, …`), which
  over ℕ is equivalent to infinitude of the set of such n.
- The readings "infinitely many pairs (n, m)", "infinitely many n",
  "infinitely many m", and "infinitely many common values a = φ(n) = σ(m)"
  are all equivalent: for fixed n ≥ 1 there are only finitely many partners m
  (σ(m) ≥ m for m ≥ 1 forces m ≤ φ(n)); for fixed m there are only finitely
  many n (φ(n) ≥ √(n/2) forces n ≤ 2·σ(m)²); and along infinitely many n the
  values φ(n) are unbounded (φ has finite fibers), giving infinitely many
  distinct common values. Hence this statement also matches the upstream
  encoding via the infinitude of the pair set (whose only pair outside
  n, m ≥ 1 is the junk pair (0, 0), since φ(n) = 0 ↔ n = 0 and
  σ(m) = 0 ↔ m = 0).
- The `0 < n` and `0 < m` conjuncts pin the intended reading "positive
  integers" and block the degenerate witness φ(0) = 0 = sumDivisors 0.

References (assembled by the Fable review; the raw input carried the keys with
no bibliography. Sources: sibling files in this corpus, the upstream
formal-conjectures repo at HEAD dd1c2beb, and — where flagged — reviewer
knowledge. No /latex/48 fetch survives in the session logs, so all entries are
honest stubs pending verification against erdosproblems.com/latex/48:
DEFERRED where noted):
- [Er59c] Erdős, P., _Remarks on number theory II. Some problems on the σ
  function_. Acta Arith. 5 (1959), 171-177. (Consistent sibling-corpus entry,
  e.g. problems 823/824.)
- [Er74b] Erdős, P., _Remarks on some problems in number theory_. Math.
  Balkanica (1974), 197-202. (Upstream formal-conjectures' canonical expansion
  for this key; a minority of sibling files expand [Er74b] differently — "On
  abundant-like numbers", Canad. Math. Bull. 17 (1974), 599-602 — so the
  attribution of this key is flagged: DEFERRED.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique 28
  (1980). (Consistent corpus + upstream entry.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Upstream-dominant
  expansion; some corpus files expand [Er95] as Congressus Numerantium 107
  (1995) instead: DEFERRED.)
- [FLP10] Ford, K., Luca, F., and Pomerance, C. (2010). (Authors and year from
  the page prose and key; the title — _Common values of the arithmetic
  functions φ and σ_, Bull. Lond. Math. Soc. — is reviewer-recalled and
  unverified offline: DEFERRED.)
- [Ga11] Garaev, M. Z. (2011). (Surname from the page prose, year from the
  key, initials reviewer-recalled; all further details DEFERRED.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd edition,
  Springer (2004). This problem: B38. (Consistent corpus + upstream entry;
  the B38 pointer from the page.)

Tags: number theory. No prize; OEIS: N/A.
Source: https://www.erdosproblems.com/48
-/
theorem erdos_problem_48 :
    ∀ N : ℕ, ∃ n m : ℕ, n ≥ N ∧ 0 < n ∧ 0 < m ∧
      totient n = sumDivisors m :=
  sorry

/--
Common-values form, the framing in which Ford, Luca, and Pomerance [FLP10]
proved the problem: there are infinitely many values a with a = φ(n) = σ(m)
for some positive integers n, m. Qualitatively equivalent to
`erdos_problem_48` (see the encoding notes there), stated here because the
page's quantitative results refine exactly this count. [FLP10] prove that at
least exp((log log x)^c) many such a ≤ x exist for an absolute constant
c > 0, and Garaev [Ga11] improved this to exp((log log x)^{ω(x)}) with
ω(x) → ∞; those quantitative forms need `Real.exp`/`Real.log` machinery not
imported by this file and are left unformalized (DEFERRED).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_48.variants.common_values :
    ∀ N : ℕ, ∃ a : ℕ, a ≥ N ∧ ∃ n m : ℕ, 0 < n ∧ 0 < m ∧
      a = totient n ∧ a = sumDivisors m :=
  sorry
