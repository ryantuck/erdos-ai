import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

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
    the difference set of every nonempty set). The ⊆-form remains the intended
    reading ("no common nonzero difference") even for degenerate empty sets,
    and every witness used below (maximum-size Sidon sets, Barreto's
    constructions) is nonempty, so the two readings agree wherever it matters. -/
def DisjointDifferences (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
    (a₁ : ℤ) - (a₂ : ℤ) = (b₁ : ℤ) - (b₂ : ℤ) → a₁ = a₂ ∧ b₁ = b₂

/--
Erdős Problem #43 [Er95] — DISPROVED (both questions answered in the
negative); it was still OPEN (with a $100 prize) when this file was first
written (erdosproblems.com/43, page last edited 20 December 2025, accessed
2026-02-22):

> If A, B ⊂ {1, ..., N} are two Sidon sets such that (A - A) ∩ (B - B) = {0}
> then is it true that
>   C(|A|, 2) + C(|B|, 2) ≤ C(f(N), 2) + O(1),
> where f(N) is the maximum possible size of a Sidon set in {1, ..., N}?
> If |A| = |B| then can this bound be improved to
>   C(|A|, 2) + C(|B|, 2) ≤ (1 - c + o(1)) · C(f(N), 2)
> for some constant c > 0?

Here S represents a maximum-size Sidon set in {1, ..., N}, so S.card = f(N),
and the O(1) term is captured by an absolute constant C (equivalent to the
"for all sufficiently large N" reading, since for each fixed N the excess is
bounded — there are only finitely many A, B ⊆ {1, ..., N}).

Status and provenance:
- At page capture (accessed 2026-02-22) the banner was OPEN. The page already
  recorded: f(N) ~ √N (see erdosproblems.com/30), so the second question is
  equivalent to asking whether |A| ≤ (1/√2 - c + o(1))√N when |A| = |B|; "In
  the comments Tao has given a proof of this upper bound without the -c"; and
  "In the comments Barreto has given a negative answer to the second question:
  for infinitely many N there exist Sidon sets A, B ⊂ {1, ..., N} with
  |A| = |B| and (A - A) ∩ (B - B) = {0} and
  C(|A|, 2) + C(|B|, 2) ≥ (1 - o(1)) · C(f(N), 2)."
- The current metadata mirror (github.com/teorth/erdosproblems,
  data/problems.yaml, commit a09c7a21, 2026-08-14) records status
  **"disproved"** (yaml last_update 2025-08-31 — a date that predates the
  captured OPEN banner and so appears not to track the banner change; the
  state field is taken as authoritative per pipeline rules).
- The upstream formal-conjectures file (FormalConjectures/ErdosProblems/43.lean,
  HEAD dd1c2beb, 2026-08-16) formalizes both questions as
  `research solved` with `answer(False)`, noting for the first: "The answer is
  no; the Erdős Problems page notes that this follows from the solution to
  Erdős Problem 42."

Why the first question's answer is NO (via Problem #42, solved affirmatively
2026, Lean-verified — see conjectures-v2/42.lean): for every M ≥ 1 and all
sufficiently large N, every maximal Sidon set A ⊆ {1, ..., N} admits a Sidon
set B ⊆ {1, ..., N} with |B| = M and no common nonzero difference. Take A of
maximum size f(N) (maximum-cardinality Sidon sets are inclusion-maximal) and
S = A; then C(|A|, 2) + C(|B|, 2) = C(f(N), 2) + C(M, 2), which exceeds
C(f(N), 2) + C as soon as C(M, 2) > C (e.g. M = C + 2). So no absolute
constant C works.

The theorem below states the true (refuted) direction ([defect] fix, not
compile-verified): it is the classical negation of the first-pass file's
assertion `∃ C, ∀ N A B S, hyps → C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + C`,
with the negation pushed inward (for every C a witnessing configuration
exists). All hypotheses and the inequality are byte-compatible with the
original encoding; only the quantifier polarity is flipped.

References ([Er95] is the page's sole citation key; the /latex/43 fetches
preserved in the session logs contain no bibliography entries, so this is an
honest stub — full data DEFERRED):
- [Er95] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_ (1995). (Corpus-majority title; sibling files disagree on the
  venue — most give "Combinatorics '94 (Catania), Congressus Numerantium 107
  (1995)", others "Combinatorics, Paul Erdős is Eighty 2 (1996), 1-25" or
  "Some of my favourite problems in number theory, combinatorics, and
  geometry, Resenhas 1 (1995), 165-186" — so no venue is asserted here;
  unverified offline.)

Tags: number theory | sidon sets | additive combinatorics. Prize: $100.
Related OEIS sequences: A143824, A227590, A003022. Cross-references:
erdosproblems.com/30 (f(N) ~ √N) and erdosproblems.com/42 (source of the
disproof of the first question). Additional thanks to: Kevin Barreto and
Terence Tao. Source: https://www.erdosproblems.com/43
-/
theorem erdos_problem_43 :
    ∀ C : ℕ, ∃ (N : ℕ) (A B S : Finset ℕ),
      IsSidonSet A ∧ IsSidonSet B ∧ IsSidonSet S ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
      (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) ∧
      (∀ T : Finset ℕ, IsSidonSet T → (∀ t ∈ T, 1 ≤ t ∧ t ≤ N) → T.card ≤ S.card) ∧
      DisjointDifferences A B ∧
      Nat.choose S.card 2 + C < Nat.choose A.card 2 + Nat.choose B.card 2 :=
  sorry

/--
Second question of Erdős Problem #43 [Er95], answered in the NEGATIVE by
Barreto (page-confirmed; recorded upstream as `answer(False)`): the bound
cannot be improved to (1 - c + o(1)) · C(f(N), 2) for any constant c > 0,
because for infinitely many N there exist Sidon sets A, B ⊆ {1, ..., N} with
|A| = |B|, (A - A) ∩ (B - B) = {0}, and
C(|A|, 2) + C(|B|, 2) ≥ (1 - o(1)) · C(f(N), 2).

Encoding of the (1 - o(1)) lower bound without real-number machinery: for
every k ≥ 1 and every threshold N₀ there are N ≥ N₀ and such sets with
k · (C(|A|, 2) + C(|B|, 2)) ≥ (k - 1) · C(f(N), 2), i.e.
C(|A|, 2) + C(|B|, 2) ≥ (1 - 1/k) · C(f(N), 2). The ∀k-infinitely-often form
is equivalent to the single-(1 - o(1))-sequence form by monotone
diagonalization (the property weakens as k decreases; pick N_k increasing for
ε = 1/k). The ℕ-subtraction k - 1 is guarded by 1 ≤ k, so no truncation
occurs. This statement refutes the asked improvement: if some c > 0 worked,
then eventually every admissible pair would satisfy
C(|A|, 2) + C(|B|, 2) ≤ (1 - c/2) · C(f(N), 2), contradicting the k-witnesses
for any k > 2/c (note C(f(N), 2) > 0 for N ≥ 2 since {1, 2} is Sidon).

NOTE: this variant was added by the Fable review ([defect]-level omission —
the second question of the source problem was not formalized at all) and is
NOT compile-verified. Barreto's construction has (A - A) ∩ (B - B) exactly
{0}; the ⊆-form `DisjointDifferences` conjunct asserted here is implied by it.
-/
theorem erdos_problem_43.variants.equal_size_barreto :
    ∀ k : ℕ, 1 ≤ k → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ (A B S : Finset ℕ),
        IsSidonSet A ∧ IsSidonSet B ∧ IsSidonSet S ∧
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
        (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
        (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) ∧
        (∀ T : Finset ℕ, IsSidonSet T → (∀ t ∈ T, 1 ≤ t ∧ t ≤ N) → T.card ≤ S.card) ∧
        A.card = B.card ∧
        DisjointDifferences A B ∧
        (k - 1) * Nat.choose S.card 2 ≤ k * (Nat.choose A.card 2 + Nat.choose B.card 2) :=
  sorry

/--
Tao's partial result on the second question (page-confirmed): since
f(N) ~ √N, the asked improvement is equivalent to
|A| ≤ (1/√2 - c + o(1))√N for equal-size pairs, and "In the comments Tao has
given a proof of this upper bound without the -c": if A, B ⊆ {1, ..., N} are
Sidon with |A| = |B| and no common nonzero difference, then
|A| ≤ (1/√2 + o(1))√N.

Encoding without real-number machinery, via squaring (monotone, so the
o(1)-statements are equivalent): |A| ≤ (1/√2 + o(1))√N iff
|A|² ≤ (1/2 + o(1))N iff for every k ≥ 1, eventually in N,
2k · |A|² ≤ (k + 2) · N (the ε = 1/k instance, since
(1/2 + 1/k) · N = ((k + 2)/(2k)) · N).

NOTE: this variant was added by the Fable review (optional enrichment,
page-confirmed) and is NOT compile-verified.
-/
theorem erdos_problem_43.variants.tao_upper_bound :
    ∀ k : ℕ, 1 ≤ k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (A B : Finset ℕ),
        IsSidonSet A → IsSidonSet B →
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
        A.card = B.card →
        DisjointDifferences A B →
        2 * k * (A.card * A.card) ≤ (k + 2) * N :=
  sorry
