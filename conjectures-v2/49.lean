import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/--
Erdős Problem #49 [Er95] [Er95c] — PROVED
(erdosproblems.com/49, accessed 2026-02-22; no page-edition date in the capture):

"Let A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N} be such that φ(a₁) < ⋯ < φ(aₜ). The primes
are such an example. Are they the largest possible? Can one show that
|A| < (1 + o(1))π(N) or even |A| = o(N)?"

Here φ is the Euler totient function and π is the prime counting function; the
condition says φ is strictly increasing on A in the ordering inherited from ℕ.
Solved by Tao [Ta23b], who proved the quantitative bound
|A| ≤ (1 + O((log log x)⁵ / log x)) · π(x); the qualitative corollary
|A| ≤ (1 + o(1))π(N) formalized below is the affirmative answer to the page's
question, i.e., the primes are (asymptotically) the largest possible example.
The statement unfolds the o(1) in the standard way: for every ε > 0, for all
sufficiently large N, any such A satisfies |A| ≤ (1 + ε) · π(N). (The page's
strict "<" and this "≤" are interchangeable inside a (1 + o(1)) bound.)

Page remarks (recovered): Erdős remarks that the last conjecture (|A| = o(N),
formalized as `erdos_problem_49.variants.weaker_o_N` below) is probably easy,
and that similar questions can be asked about σ(n); in [Er95c] Erdős further
asks about the situation when φ(a₁) ≤ ⋯ ≤ φ(aₜ) (see
`erdos_problem_49.variants.nonstrict` below). The σ(n) analogue is left
unformalized: the page records only that the question can be asked, not a
conjectured answer, so any specific bound would go beyond the source.

Status and provenance:
- Page banner at capture: PROVED, tooltip "This has been solved in the
  affirmative."
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "proved", last update 2025-08-31;
  no prize; OEIS: A365339, A365474; formalized: no; tags: number theory,
  primes.
- The upstream formal-conjectures repo (HEAD dd1c2beb, 2026-08-16) has no
  ErdosProblems/49.lean, consistent with the page's "Formalised statement? No".

References (assembled by the Fable review; the raw input carried no keys):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Key and its use
  from the recovered page; this expansion is the upstream-dominant one — some
  corpus files expand [Er95] as "Some of my favourite problems in various
  branches of combinatorics", Congressus Numerantium 107 (1995) instead, and
  the styled copy of this problem uses that reading; venue/volume
  verification: DEFERRED.)
- [Er95c] Erdős, P., _Some problems in number theory_. Octogon Math. Mag.
  (1995), 3-5. (From the original pipeline's fetch of
  erdosproblems.com/latex/49, recovered from the session logs; volume absent
  there: DEFERRED.)
- [Ta23b] Tao, T., _Monotone non-decreasing sequences of the Euler totient
  function_. arXiv:2309.02325 (2023). (Same recovered /latex/49 fetch.)

Tags: number theory, primes. No prize.
Related OEIS sequences: A365339, A365474 (contents unverified offline).
Source: https://www.erdosproblems.com/49
-/
theorem erdos_problem_49 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) :=
  sorry

/--
The weaker bound asked in the same breath by the page ("or even |A| = o(N)?"),
which Erdős remarks is probably easy: any A ⊆ {1, …, N} on which φ is strictly
increasing satisfies |A| = o(N), unfolded as: for every ε > 0, for all
sufficiently large N, |A| ≤ ε · N. This is implied by `erdos_problem_49`
together with π(N) = o(N), and is in particular also solved (Tao [Ta23b]).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_49.variants.weaker_o_N :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b) →
      (A.card : ℝ) ≤ ε * (N : ℝ) :=
  sorry

/--
The non-strict variant from [Er95c]: the same (1 + o(1))π(N) bound when the
condition is weakened to φ(a₁) ≤ ⋯ ≤ φ(aₜ), i.e., a < b → φ(a) ≤ φ(b) on A
(so more sets A qualify, and the bound is a stronger assertion than
`erdos_problem_49`).

Epistemic status, flagged honestly: the recovered page says only that Erdős
"further asks about the situation when φ(a₁) ≤ ⋯ ≤ φ(aₜ)" in [Er95c], without
recording an answer. The title of Tao's paper [Ta23b], recovered from the
/latex/49 fetch — "Monotone non-decreasing sequences of the Euler totient
function" — indicates that the non-decreasing case is precisely what that
paper treats, so this bound is very likely Tao's actual theorem (from which
the strict case of `erdos_problem_49` follows a fortiori); but the page itself
does not state this, so the attribution of THIS variant's truth is
reviewer-inferred from the recovered title, not page-verified. The styled
corpus copy (deepmind/deepmind/49.lean) states the same proposition and tags
it open.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_49.variants.nonstrict :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ x ∈ A, 1 ≤ x ∧ x ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a ≤ Nat.totient b) →
      (A.card : ℝ) ≤ (1 + ε) * (Nat.primeCounting N : ℝ) :=
  sorry
