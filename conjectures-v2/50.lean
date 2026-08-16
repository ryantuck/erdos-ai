import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic

open Nat Finset Filter Set Classical

/--
Count of natural numbers n in {1, ..., N} with φ(n) < c · n.

Notes (Fable review):
- `Finset.range (N + 1)` is {0, …, N}; the `0 < n` conjunct restricts to
  {1, …, N}. The guard is belt-and-braces: n = 0 could never be counted anyway,
  since `(Nat.totient 0 : ℝ) = 0 < c * 0 = 0` is false for every c.
- The predicate compares in ℝ, and `<` on ℝ is not decidable, so
  `Finset.filter` elaborates via `Classical.propDecidable` (from the `open
  Classical`) — this is why the definition is `noncomputable`.
- At c = 0 the count is 0 for every N (density 0); at c = 1 it counts all of
  {2, …, N} (φ(n) < n for n ≥ 2, while φ(1) = 1), giving density 1.
-/
noncomputable def totientDensityCount (c : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => 0 < n ∧ (Nat.totient n : ℝ) < c * ↑n)).card

/--
Erdős Problem #50 [Er95, p.171] — OPEN, $250 prize
(erdosproblems.com/50, accessed 2026-02-22):

"Schoenberg proved that for every c ∈ [0,1] the density of
{n ∈ ℕ : φ(n) < cn} exists. Let this density be denoted by f(c). Is it true
that there are no x such that f'(x) exists and is positive?"

Page remark: "Erdős [Er95] could prove the distribution function is purely
singular." Pure singularity (f' = 0 Lebesgue-almost everywhere) does NOT
settle the question: the question asks that no point at all — not just almost
no point — carries a positive derivative, and a singular monotone function can
a priori still have such exceptional points. The problem is open precisely for
this reason.

Status and provenance:
- Page banner at capture: OPEN, tooltip "This is open, and cannot be resolved
  with a finite computation." Prize $250. Tags: number theory. No OEIS entry,
  no cross-referenced problems, 0 comments.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  commit a09c7a2, 2026-08-14) agrees: state "open", last update 2025-08-31;
  prize $250; OEIS: N/A; formalized: yes (2026-03-19); tags: number theory.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/50.lean,
  HEAD dd1c2beb, 2026-08-16) marks `erdos_50` as `research open` and states
  `answer(sorry) ↔ ∀ᵉ (f : ℝ → ℝ) (hf : IsDistributionOfPhiRatio f),
  ¬∃ x ∈ Icc (0 : ℝ) 1, ∃ y > 0, HasDerivWithinAt f y (Icc 0 1) x`.
- This corpus has no `answer()` elaborator; the direct assertion below states
  the conjectured "yes" direction of the open yes/no question (hence the
  `_conjecture` suffix).

Encoding notes (Fable review):
- FIX (defect, not compile-verified): the original input quantified the
  conclusion over ALL x : ℝ, but the hypothesis pins f only on [0,1]; any
  satisfying f extended linearly outside [0,1] (e.g. f(x) = x for x < 0) has
  derivative 1 there, so the unrestricted statement was provably false. The
  conclusion is now restricted to x ∈ Icc 0 1, matching the function's domain.
- Endpoint semantics: at x = 0 (resp. x = 1), `HasDerivAt` is two-sided and
  sees the unpinned values of f outside [0,1]; because f is universally
  quantified over all extensions, "∃ extension with HasDerivAt f d x" is
  equivalent to "the pinned one-sided difference quotient tends to d" (an
  adversary matches the free side linearly with slope d). So the ∀f-form with
  `Icc` asserts exactly: the true distribution function has no positive
  derivative on (0,1) and no positive one-sided derivative at 0 or 1 — the
  faithful reading of the question on the domain [0,1]. For interior x all
  satisfying f agree near x, so no extension freedom arises there. This makes
  the statement equivalent to the upstream `HasDerivWithinAt … (Icc 0 1)`
  encoding.
- `∀ d, HasDerivAt f d x → d ≤ 0` is literally "no d > 0 is a derivative of f
  at x", i.e. "f'(x) does not exist positive". Since f is non-decreasing
  (densities of nested sets), any existing derivative is ≥ 0, so the content
  is: wherever f' exists on [0,1], f' = 0 — the everywhere version of
  singularity asked by the problem.
- The N = 0 term of the density quotient divides by ↑N = 0 and yields Lean's
  junk value 0; harmless inside `Tendsto … atTop`.

References (assembled by the Fable review; the raw input carried no keys and
no bibliography. Sources: the page's citation line `#50: [Er95,p.171]`; the
bibliographic fetch logged in the upstream fix session
(claude-session-logs-formal-conjectures/df38357b), which gives journal, year,
and pages for [Er95]; the upstream formal-conjectures HEAD; sibling corpus
files. Honest stubs pending verification against erdosproblems.com/latex/50:
DEFERRED where noted):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. This problem:
  p. 171. (Journal/year/pages from the logged bibliography fetch; the volume
  number — "1" in some corpus entries, absent upstream — is unconfirmed:
  DEFERRED.)
- [Sch36] Schoenberg, I. J., _On asymptotic distributions of arithmetical
  functions_. Trans. Amer. Math. Soc. 39 (1936), 315-330. (Not cited on the
  page, which names Schoenberg only in prose; entry from the upstream
  formal-conjectures bibliography, which however labels the key "[Sch38]"
  against its own 1936 data — key normalized here to the year: DEFERRED.)

Tags: number theory. Prize: $250. OEIS: N/A.
Source: https://www.erdosproblems.com/50
-/
theorem erdos_problem_50_conjecture :
    ∀ f : ℝ → ℝ,
      (∀ c ∈ Icc (0 : ℝ) 1,
        Tendsto (fun N : ℕ => (totientDensityCount c N : ℝ) / ↑N) atTop (nhds (f c))) →
      ∀ x ∈ Icc (0 : ℝ) 1, ∀ d : ℝ, HasDerivAt f d x → d ≤ 0 :=
  sorry

/--
Schoenberg's theorem, quoted as given on the problem page: for every
c ∈ [0,1] the natural density of {n ∈ ℕ : φ(n) < cn} exists — i.e. there is a
distribution function f satisfying the hypothesis of
`erdos_problem_50_conjecture`. Solved (Schoenberg [Sch36]). This is the
statement that makes the main conjecture non-vacuous.

Erdős's complementary result — that this f is purely singular (continuous with
f' = 0 almost everywhere) [Er95] — needs measure-theoretic vocabulary
(`∀ᵐ x ∂volume`) not imported by this file and is recorded here in prose only
(DEFERRED; upstream formalizes it as `erdos_50_singular`).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_50_conjecture.variants.schoenberg :
    ∃ f : ℝ → ℝ, ∀ c ∈ Icc (0 : ℝ) 1,
      Tendsto (fun N : ℕ => (totientDensityCount c N : ℝ) / ↑N) atTop (nhds (f c)) :=
  sorry
