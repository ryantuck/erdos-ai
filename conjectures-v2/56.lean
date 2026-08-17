import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

/-!
# Erdős Problem 56

*Reference:* [erdosproblems.com/56](https://www.erdosproblems.com/56)
(accessed 2026-03-05, page edition 06 December 2025; page content recovered from two
agreeing archived session-log captures (raw `html/56.html` and tidied `tidy/56.html`)
— the live site is unreachable from the review container).

Statement (verbatim from the site): "Let $N\geq p_k$ where $p_k$ is the $k$th prime.
Suppose $A\subseteq \{1,\ldots,N\}$ is such that there are no $k+1$ elements of $A$
which are relatively prime. An example is the set of all multiples of the first $k$
primes. Is this the largest such set?" [Er65][Er73][Er92b][Er92c][Er95] — $10 prize.

Status: **DISPROVED (LEAN)** ("This has been solved in the negative and the proof
verified in Lean"). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
checked at commit a09c7a2, 2026-08-14) agrees: status "disproved (Lean)", last update
2025-11-26; prize $10; formalized: yes (2025-08-31); tags: number theory, intersecting
family; OEIS: N/A. The upstream google-deepmind/formal-conjectures repository (HEAD
dd1c2beb, 2026-08-16) carries `FormalConjectures/ErdosProblems/56.lean` stating
`answer(False) ↔ ∀ᵉ (k > 0) (N ≥ (k-1).nth Nat.Prime), MaxWeaklyDivisible N k =
(FirstPrimesMultiples N k).card`, tagged with a machine-checked formal disproof at
plby/lean-proofs (`src/v4.24.0/ErdosProblems/Erdos56.lean`, witness $k = 212$,
$N = p_{209}\,p_{218}$).

Remarks from the page: this was disproved for $k=212$ by Ahlswede and Khachatrian
[AhKh94], who suggest that their methods can disprove this for arbitrarily large $k$.
Erdős later asked ([Er92b] and [Er95]) if the conjecture remains true provided
$N\geq (1+o(1))p_k^2$ (or, in a weaker form, whether it is true for $N$ sufficiently
large depending on $k$). Ahlswede and Khachatrian [AhKh95] proved this latter claim:
for any fixed $k$, if $N$ is sufficiently large depending on $k$ then the largest such
set is the set of all multiples of the first $k$ primes. See also [534]. This is
discussed in problem B26 of Guy's collection [Gu04]. Additional thanks: Zachary Chase
and Dustin Mixon. 6 comments on the problem (contents not in the archive).

References (no `/latex/56` fetch survives in the logs; provenance per entry):

- [Er65] Erdős, P., _Extremal problems in number theory_. Proc. Sympos. Pure Math.,
  Vol. VIII (1965), 181–189. (Corpus- and upstream-consensus entry; DEFERRED against
  the live `/latex/56` source.)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
  Colo., 1971) (1973), 117–138. (Corpus- and upstream-consensus entry; DEFERRED.)
- [Er92b] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Matematiche (Catania) 47 (1992), 231–240. (Corpus- and
  upstream-consensus entry; DEFERRED.)
- [Er92c] Erdős, P., _Some of my forgotten problems in number theory_.
  Hardy-Ramanujan J. (1992), 34–50. (Upstream-consensus entry; a minority of sibling
  corpus files expand this key with the [Er92b] title instead — conflict noted,
  DEFERRED.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics,
  and geometry_. Resenhas (1995), 165–186. (Corpus- and upstream-dominant entry;
  DEFERRED.)
- [AhKh94] Ahlswede, R. and Khachatrian, L. H., _On extremal sets without coprimes_.
  Acta Arith. 66 (1994), no. 1, 89–99. (Verified against the header of the
  Lean-verified disproof, plby/lean-proofs `Erdos56.lean`, fetched 2026-08-16.)
- [AhKh95] Ahlswede, R. and Khachatrian, L. H. (1995). (Key and authors from the page;
  full bibliographic data not recoverable offline — DEFERRED. Reviewer knowledge
  suggests _Maximal sets of numbers not containing $k+1$ pairwise coprime integers_,
  Acta Arith. 72 (1995), 77–100; unverified, not to be relied on.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed., Springer (2004),
  xviii+437. Problem B26. (Corpus-consensus entry; DEFERRED.)
-/

open Nat Finset

noncomputable section

/--
A finset S of natural numbers is **pairwise coprime** if every two distinct
elements of S have gcd equal to 1.
-/
def PairwiseCoprime (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.Coprime a b

/--
The set A has no k+1 pairwise coprime elements: there is no subset of A
of size k+1 whose elements are pairwise coprime.

Degenerate case: for `k = 0` every singleton subset is (vacuously) pairwise
coprime, so `NoPairwiseCoprimeSubset A 0` forces `A = ∅`; the problem intends
`k ≥ 1`, which the main theorem below makes explicit.
-/
def NoPairwiseCoprimeSubset (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = k + 1 → ¬PairwiseCoprime S

/--
The set of all multiples of the first k primes in {1,…,N}: that is,
{n ∈ {1,…,N} | ∃ i < k, (the i-th prime, 0-indexed) divides n}.

[defect fix, not compile-verified] The first-pass definition was
`(Finset.range N).filter fun m => ∃ i < k, (nth Nat.Prime i) ∣ (m + 1)` — the
*shifted* copy {n − 1 : n ∈ {1,…,N}, some pᵢ ∣ n}, which has the right
cardinality (the map m ↦ m + 1 is a bijection onto this set) but is **not** the
set its docstring describes, and in particular is not itself an example of a set
with no k+1 pairwise coprime elements (for k = 1, N = 4 it is {1, 3}, whose two
elements are coprime). This corrected definition contains the actual multiples
(the guard `1 ≤ n` excludes 0, which every prime divides), so the theorem
statements below are unchanged in meaning where only the cardinality is used,
and the page's sentence "an example is the set of all multiples of the first k
primes" is true of the defined object (see the `example_admissible` variant).
-/
def multiplesOfFirstKPrimes (N k : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n =>
    1 ≤ n ∧ ∃ i : ℕ, i < k ∧ (nth Nat.Prime i) ∣ n

/--
Erdős Problem #56 [Er65, Er73, Er92b, Er92c, Er95] (DISPROVED):

> Let N ≥ p_k where p_k is the k-th prime. Suppose A ⊆ {1,…,N} is such that
> there are no k+1 elements of A which are relatively prime. An example is
> the set of all multiples of the first k primes. Is this the largest such set?

The answer is **no**: this was disproved for k = 212 by Ahlswede and
Khachatrian [AhKh94], who suggest that their methods can disprove it for
arbitrarily large k. The disproof has been machine-verified in Lean
(plby/lean-proofs, witness k = 212, N = p₂₀₉·p₂₁₈).

This direct assertion states the true (refuted) direction ([defect] fix, not
compile-verified): there exist k ≥ 1, N ≥ p_k and A ⊆ {1,…,N} with no k+1
pairwise coprime elements which is *strictly larger* than the set of multiples
of the first k primes in {1,…,N}. It is the negation (with the witnessed
strict inequality in place of ¬≤) of the universal bound
`∀ N k A, … → A.card ≤ (multiplesOfFirstKPrimes N k).card` that the question
asks about — and which the first-pass file wrongly asserted. `p_k` (1-indexed)
is `nth Nat.Prime (k - 1)` (0-indexed `Nat.nth`); the truncated subtraction is
safe under the conjunct `0 < k`.

Erdős later asked ([Er92b], [Er95]) whether the conjecture holds for
N ≥ (1+o(1))p_k² (apparently still open; not formalized here because the o(1)
encoding over k is ambiguous), or, in a weaker form, for N sufficiently large
depending on k — proved by Ahlswede and Khachatrian [AhKh95]; see the
`sufficiently_large_N` variant.
-/
theorem erdos_problem_56 :
    ∃ (N k : ℕ) (A : Finset ℕ),
      0 < k ∧
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      nth Nat.Prime (k - 1) ≤ N ∧
      NoPairwiseCoprimeSubset A k ∧
      (multiplesOfFirstKPrimes N k).card < A.card :=
  sorry

/--
Page-confirmed part of the problem statement (not compile-verified): "an example
is the set of all multiples of the first k primes" — the multiples of the first
k primes in {1,…,N} themselves contain no k+1 pairwise coprime elements (any
k+1 of them have two sharing one of the k primes, by pigeonhole, and hence a
common factor ≥ 2). This is what makes "is this the largest such set?"
well-posed. (With the first-pass shifted definition this statement would be
false — see the definition's docstring.)
-/
theorem erdos_problem_56.variants.example_admissible :
    ∀ N k : ℕ, NoPairwiseCoprimeSubset (multiplesOfFirstKPrimes N k) k :=
  sorry

/--
Page-confirmed variant (not compile-verified), proved by Ahlswede and
Khachatrian [AhKh95]: for any fixed k ≥ 1, if N is sufficiently large depending
on k, then the largest subset of {1,…,N} with no k+1 pairwise coprime elements
is the set of all multiples of the first k primes — i.e. every such subset has
at most that many elements.
-/
theorem erdos_problem_56.variants.sufficiently_large_N :
    ∀ k : ℕ, 0 < k →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A : Finset ℕ,
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          NoPairwiseCoprimeSubset A k →
          A.card ≤ (multiplesOfFirstKPrimes N k).card :=
  sorry
