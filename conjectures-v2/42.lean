import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Two sets A, B have no common nonzero difference: the only integer expressible
    both as a₁ - a₂ (a₁, a₂ ∈ A) and as b₁ - b₂ (b₁, b₂ ∈ B) is 0. Differences
    are taken in ℤ, so no ℕ-subtraction truncation occurs. In set language this
    is (A - A) ∩ (B - B) ⊆ {0}; it is equivalent to the source's
    (A - A) ∩ (B - B) = {0} exactly when A and B are both nonempty (0 lies in
    the difference set of every nonempty set), which holds wherever the theorems
    below use it with |B| = M ≥ 1 — and the ⊆-form remains the intended reading
    ("no common nonzero difference") even for the degenerate A = ∅. -/
def DisjointDifferences (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
    (a₁ : ℤ) - (a₂ : ℤ) = (b₁ : ℤ) - (b₂ : ℤ) → a₁ = a₂ ∧ b₁ = b₂

/--
Erdős Problem #42 [Er95] — SOLVED (in the affirmative, with a Lean-verified
proof); it was still OPEN when this file was first written
(erdosproblems.com/42, page last edited 23 January 2026, accessed 2026-03-05):

Let M ≥ 1 and N be sufficiently large in terms of M. Is it true that for every
Sidon set A ⊆ {1, ..., N} there is another Sidon set B ⊆ {1, ..., N} of size M
such that (A - A) ∩ (B - B) = {0}?

The statement is: for every M ≥ 1 there exists N₀ such that for all N ≥ N₀ and
every Sidon set A ⊆ {1, ..., N}, there exists a Sidon set B ⊆ {1, ..., N} with
|B| = M and (A - A) ∩ (B - B) = {0}.

Status and provenance:
- At page capture (accessed 2026-03-05) the banner was OPEN, with the remark:
  "Sedov in the comments (using ChatGPT and Codex) has proved this is true for
  M = 3. The case M = 1 is trivial; the case M = 2 is a little less trivial,
  but is also proved by Sedov in the comments."
- The current metadata mirror (github.com/teorth/erdosproblems,
  data/problems.yaml, commit a09c7a21, 2026-08-14) records status
  "solved (Lean)", last updated 2026-05-10.
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/42.lean,
  HEAD dd1c2beb, 2026-08-16) marks `erdos_42` as `research solved` with
  `answer(True)`: "This was proved for all M by GPT 5.5 Pro (prompted by
  Sandhu), see discussion thread for more details", carrying a
  `formal_proof using lean4` attribute pointing at
  github.com/Shashi456/erdos-formalizations (Erdos/P42/CompactCayley/Proof.lean).
Hence the direct assertion below is the proved (true) direction of the
question.

Universe of A: this file quantifies over *every* Sidon set A ⊆ {1, ..., N},
exactly as the problem page states. The upstream formalization instead
quantifies over *maximal* Sidon sets in {1, ..., N}. The two readings are
equivalent: any Sidon A ⊆ {1, ..., N} extends to a maximal Sidon
A' ⊇ A within {1, ..., N} (finitely many candidates), every difference of A is
a difference of A', so any B working for A' works for A; the converse
instantiation is trivial.

References ([Er95] is the page's sole citation key; no /latex/42 capture
exists in the session logs, so the entry is an honest stub — full
journal/volume/pages DEFERRED):
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub:
  corpus-majority entry; unverified offline.)

Tags: number theory | sidon sets | additive combinatorics. No prize;
OEIS: N/A. Additional thanks to: Zach Hunter and Daniil Sedov.
Source: https://www.erdosproblems.com/42
-/
theorem erdos_problem_42 :
    ∀ (M : ℕ), 1 ≤ M →
      ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
        ∀ (A : Finset ℕ),
          IsSidonSet A →
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          ∃ (B : Finset ℕ),
            IsSidonSet B ∧
            (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
            B.card = M ∧
            DisjointDifferences A B :=
  sorry

/--
Constructive variant, after upstream `erdos_42.variants.constructive` (also
marked `research solved` there, with a Lean proof recorded at
github.com/KitaKen1/erdos-42-constructive-variant): there is a single function
f : ℕ → ℕ such that for all M ≥ 1 and all N ≥ f(M), every Sidon set
A ⊆ {1, ..., N} admits a Sidon set B ⊆ {1, ..., N} of size M with
(A - A) ∩ (B - B) = {0}. This is classically equivalent to
`erdos_problem_42` (define f M as a witnessing N₀ by choice), but records the
uniform-threshold form explicitly.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_42.variants.constructive :
    ∃ f : ℕ → ℕ, ∀ (M N : ℕ), 1 ≤ M → f M ≤ N →
      ∀ (A : Finset ℕ),
        IsSidonSet A →
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        ∃ (B : Finset ℕ),
          IsSidonSet B ∧
          (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
          B.card = M ∧
          DisjointDifferences A B :=
  sorry
