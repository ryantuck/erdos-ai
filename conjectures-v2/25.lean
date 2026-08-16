import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Order.Filter.Basic

/-!
# Erdős Problem #25

Let $1\leq n_1<n_2<\cdots$ be an arbitrary sequence of integers, each with
an associated residue class $a_i\pmod{n_i}$. Let $A$ be the set of integers
$n$ such that for every $i$ either $n<n_i$ or $n\not\equiv a_i\pmod{n_i}$.
Must the logarithmic density of $A$ exist?

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." (erdosproblems.com/25, page last edited
20 January 2026, accessed 2026-03-05; the teorth/erdosproblems metadata
mirror agrees: state "open", last update 2025-08-31.)

This is a special case of [486] (which asks the same question with an
arbitrary — not necessarily size-restricted — set of forbidden residue
classes $X_n \subseteq \mathbb{Z}/n\mathbb{Z}$ for every modulus $n$; the
statement of [486] is not on this problem's page and is therefore
documented here rather than formalized).

## References

Problem source: [Er95].

- [Er95] Erdős, P., *Some of my favourite problems in number theory,
  combinatorics, and geometry*. Resenhas 1 (1995), 165-186. (Stub: the
  page capture lists only the key `[Er95]`; no `/latex/25` or `/bibs/`
  fetch is in the session logs. Title/journal/pages from sibling corpus
  files sharing this site-global key for number-theory problems, e.g.
  `deepmind/deepmind/46.lean` and `conjectures-v2/17.lean`; the volume
  number is the corpus reading, unverified offline. A corpus minority
  resolves `[Er95]` to the Congressus Numerantium combinatorics paper;
  problem 25 is a number-theory problem, so the Resenhas reading is
  preferred, as for problems 1, 2, 7 and 17.)

No related OEIS sequences (mirror: "N/A"). No prize.
Formalised statement? Yes (upstream: google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/25.lean`; mirror records formalized "yes",
2025-12-28).

Tags: number theory
https://www.erdosproblems.com/25
-/

open Filter Set Classical

noncomputable section

/--
The logarithmic density of a set A ⊆ ℕ⁺ is defined as
  δ(A) = lim_{N→∞} (1 / log N) · ∑_{n ∈ A, 1 ≤ n ≤ N} 1/n,
when this limit exists.

(Mathlib has no logarithmic-density definition; the upstream
formal-conjectures repository's `Set.HasLogDensity`, summing
`∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / Real.log n`, is the same notion — the
extra `k = 0` term there is `(0 : ℝ)⁻¹ = 0` and the `N = 0, 1` values,
where `Real.log N = 0` and division/inversion yield `0`, are irrelevant to
the `atTop` limit.)
-/
def logDensity (A : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ =>
    (Real.log N)⁻¹ * ∑ n ∈ Finset.Icc 1 N, if n ∈ A then (n : ℝ)⁻¹ else 0)
    atTop (nhds d)

/--
Erdős Problem #25 [Er95]:

Let 1 ≤ n₁ < n₂ < ⋯ be an arbitrary sequence of integers, each with an
associated residue class aᵢ (mod nᵢ). Let A be the set of integers n such
that for every i either n < nᵢ or n ≢ aᵢ (mod nᵢ). Must the logarithmic
density of A exist?

This is a special case of problem #486.

The source poses this as a yes/no question, status OPEN. The raw pipeline
has no `answer()` elaborator; per this corpus's convention the conjectured
("yes") direction is asserted directly: for every admissible sequence of
moduli and residues, the logarithmic density of the sifted set exists.
(The sifted set is written inline in the conclusion. The first-pass file
instead introduced it as a default-valued binder `(A : Set ℕ := …)`; a
default value elaborates to `optParam` and does not constrain the bound
variable, so that statement universally quantified over an *arbitrary*
`A : Set ℕ` and was provably false — e.g. `A = ⋃ k, [2^(4^k), 2^(2·4^k))`
has lower logarithmic density 1/3 and upper logarithmic density 2/3, so no
`d` exists for it. Fixed here; not compile-verified.)
-/
theorem erdos_problem_25
    (moduli : ℕ → ℕ)
    (hmod_pos : ∀ i, 1 ≤ moduli i)
    (hmod_strict_mono : StrictMono moduli)
    (residues : ℕ → ℤ) :
    ∃ d : ℝ, logDensity
      {n : ℕ | ∀ i, n < moduli i ∨ ¬((n : ℤ) ≡ residues i [ZMOD (moduli i : ℤ)])} d :=
  sorry
