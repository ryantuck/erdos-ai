import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

open Nat Set

noncomputable section

/--
For a natural number `a` in the range of Euler's totient function,
`minTotientPreimage a h` is the smallest `n` such that `φ(n) = a`.

Note (Fable review): `Nat.find h` returns the least `n : ℕ` satisfying the
predicate, searching from `0`. Mathlib's junk value `φ(0) = 0` means that for
`a = 0` this returns `0`; for `a ≥ 1` every preimage is automatically `≥ 1`,
so the origin never interferes. By proof irrelevance the value does not
depend on the proof `h`, so quantifying over `h` in the theorem below is
harmless.
-/
def minTotientPreimage (a : ℕ) (h : ∃ n, Nat.totient n = a) : ℕ :=
  Nat.find h

/--
Erdős Problem #51 [Er95, Er98] — OPEN
(erdosproblems.com/51, accessed 2026-03-05; page last edited 2025-09-30):

"Is there an infinite set $A \subset \mathbb{N}$ such that for every
$a \in A$ there is an integer $n$ such that $\phi(n) = a$, and yet if $n_a$
is the smallest such integer then $n_a/a \to \infty$ as $a \to \infty$?"

Page remarks: Carmichael has asked whether there is an integer $t$ for which
$\phi(n) = t$ has exactly one solution. Erdős has proved that if such a $t$
exists then there must be infinitely many such $t$ (formalized as the
variant below). The page notes its remarks are the same as those of problem
[694] (see also). This is discussed in problems B36 and B39 of Guy's
collection [Gu04].

Status and provenance:
- Page banner at capture: OPEN, tooltip "This is open, and cannot be
  resolved with a finite computation." Tags: number theory. No prize.
  9 forum comments.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "open", last update 2025-08-31;
  OEIS A002202, A014197; tags: number theory; formalized upstream
  (2025-09-25).
- The upstream formal-conjectures file
  (FormalConjectures/ErdosProblems/51.lean, HEAD dd1c2beb) tags `erdos_51`
  `research open` and states `answer(sorry) ↔ ∃ A : Set ℕ, ∃ n : A → ℕ,
  A.Infinite ∧ (∀ a : A, IsLeast (φ ⁻¹' {(a : ℕ)}) (n a)) ∧
  Tendsto (fun a : A => (n a : ℝ) / (a : ℝ)) atTop atTop` — semantically the
  same proposition as the statement below.
- This corpus has no `answer()` elaborator; the direct assertion below
  states the affirmative (conjectured) direction of this open yes/no
  question, the corpus norm for open problems.

Encoding notes (Fable review):
- The limit clause unfolds "$n_a/a \to \infty$ as $a \to \infty$ within $A$"
  as `∀ C > 0, ∃ N, ∀ a ∈ A, a ≥ N → n_a/a ≥ C`. For infinite (hence
  unbounded) `A ⊆ ℕ` this is exactly `Tendsto … atTop atTop` along the
  subtype filter, and the restriction to positive `C` loses nothing: a ratio
  that is eventually `≥ 1` is eventually `≥ C` for every `C ≤ 0`.
- The inner `∀ (h : ∃ n, φ(n) = a)` re-quantifies the existence already
  guaranteed by the second conjunct; by proof irrelevance
  `minTotientPreimage a h` does not depend on `h`, so this is equivalent to
  instantiating at that witness — harmless, mildly redundant.
- Division happens in ℝ. Only `a = 0` could divide by zero (yielding Lean's
  junk value `0`); `0 ∈ A` is possible (via `φ(0) = 0`) but the limit clause
  is only constrained for `a ≥ N` and any prover takes `N ≥ 1`, so the junk
  value cannot make any conjunct spuriously true or false.

References (assembled by the Fable review; the raw input used the keys with
no bibliography. The page cites `[Er95][Er98]` with no page numbers; no
`/latex/51` payload exists in the session logs, so these are honest stubs
from sibling corpus files and upstream — DEFERRED where noted):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Corpus-dominant
  expansion of this key; some corpus files instead expand [Er95] as "Some of
  my favourite problems in various branches of combinatorics", Congressus
  Numerantium 107 (1995). Venue/volume verification: DEFERRED.)
- [Er98] Erdős, P., _Some of my new and almost new problems and results in
  combinatorial number theory_. Number theory (Eger, 1996) (1998), 169-180.
  (Consistent across sibling corpus files 1/12/18; volume data: DEFERRED.)
- [Gu04] Guy, R. K., _Unsolved Problems in Number Theory_. 3rd ed., Problem
  Books in Mathematics, Springer-Verlag, New York, 2004. (From sibling
  corpus files; the page's remark places this problem at B36 and B39 there.
  DEFERRED.)

Tags: number theory. Prize: none.
OEIS: A002202 (values taken by φ), A014197 (number of m with φ(m) = n) —
sequence contents unverifiable offline: DEFERRED.
Cross-references: [694].
Source: https://www.erdosproblems.com/51
-/
theorem erdos_problem_51 :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a ∈ A, ∃ n, Nat.totient n = a) ∧
      ∀ C : ℝ, 0 < C →
        ∃ N : ℕ, ∀ a ∈ A, a ≥ N →
          ∀ (h : ∃ n, Nat.totient n = a),
            (↑(minTotientPreimage a h) : ℝ) / (↑a : ℝ) ≥ C :=
  sorry

/--
Erdős's theorem quoted in the page remarks: "Carmichael has asked whether
there is an integer $t$ for which $\phi(n) = t$ has exactly one solution.
Erdős has proved that if such a $t$ exists then there must be infinitely
many such $t$." Solved (Erdős; the page attaches no citation key to this
result, so none is attached here).

Encoding note (Fable review): the guard `0 < t` is essential. Mathlib's junk
value `φ(0) = 0` makes `n = 0` the unique solution of `φ(n) = 0`, so without
the guard the hypothesis would be trivially true via `t = 0`, and the
statement would collapse into the unconditional assertion that Carmichael's
conjecture fails — not Erdős's conditional theorem. With `t ≥ 1` every
solution automatically satisfies `n ≥ 1`, matching the intended reading over
positive integers.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_51.variants.erdos_unique_totient_value :
    (∃ t : ℕ, 0 < t ∧ ∃! n : ℕ, Nat.totient n = t) →
      {t : ℕ | 0 < t ∧ ∃! n : ℕ, Nat.totient n = t}.Infinite :=
  sorry
