import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem 26

*Reference:* [erdosproblems.com/26](https://www.erdosproblems.com/26)
(archived capture accessed 2026-03-05; page last edited 07 December 2025)

**Problem (verbatim from the source page):** "Let $A\subset\mathbb{N}$ be
infinite. Must there exist some $k\geq 1$ such that almost all integers have a
divisor of the form $a+k$ for some $a\in A$?"

Cited on the page as [Er95, p.167].

**Status:** DISPROVED (LEAN) ("This has been solved in the negative and the
proof verified in Lean."). The teorth/erdosproblems metadata mirror (clone of
2026-08-16, entry 26) agrees: status "disproved (Lean)" (informal state
"disproved", formal status "Lean", both last updated 2025-12-28), formalized
"yes" (2025-11-25), no prize, OEIS: N/A, tags: number theory, divisors.

**Remarks (from the source page):** Asked by Erdős and Tenenbaum. Ruzsa gave
the following simple counterexample: let $A=\{n_1<n_2<\cdots\}$ where
$n_l \equiv -(k-1) \pmod{p_k}$ for all $k\leq l$, where $p_k$ denotes the
$k$th prime. A sequence $A$ is a Behrend sequence if almost all integers have
a divisor in $A$, so that this question asks whether, for every infinite set
$A$, there exists $k\geq 1$ such that $A+k$ is a Behrend sequence. Davenport
and Erdős [DaEr51] (see also Tenenbaum [Te13]) showed that $\sum \frac1a =
\infty$ for every Behrend sequence $A$, which immediately implies the answer
to this question is no (taking $A$ any infinite sequence with
$\sum\frac1a < \infty$). (It is therefore strange why Erdős asked this
question over 40 years later.) In the comments van Doorn explains how Ruzsa's
construction above can be modified to produce a counterexample with
$\sum\frac1a = \infty$. Tenenbaum asked the weaker variant where for every
$\epsilon>0$ there is some $k=k(\epsilon)$ such that at least $1-\epsilon$
density of all integers have a divisor of the form $a+k$ for some $a\in A$.

**Upstream formalization notes** (google-deepmind/formal-conjectures
`ErdosProblems/26.lean`, log capture of the original pipeline session and a
fresh sparse clone at HEAD dd1c2be, 2026-08-16): upstream states the headline
question restricted to *thick* $A$ (those with $\sum_{a\in A} 1/a = \infty$ —
the only interesting case, since [DaEr51] settles thin $A$), with
`answer(False)`; it was "formalized in Lean by Alexeev using Aristotle" and
carries a `formal_proof` link (plby/lean-proofs `Erdos26.lean`) — this is the
Lean-verified disproof behind the page's DISPROVED (LEAN) banner. The page
capture (2026-03-05) records Tenenbaum's weaker variant as *still open*, but
upstream at HEAD (2026-08-16, fresher) marks it solved with `answer(False)`:
"The DeepMind prover agent has found a formal disproof of this statement"
(formal_proof link into the mo271/formal-conjectures fork). The Tenenbaum
variant below asserts that negative resolution on upstream's authority; the
status conflict is recorded here deliberately.

**Source citation keys** (from the page): [Er95] (problem source, p.167);
[DaEr51], [Te13] (cited in the remarks).

## References

Provenance: no fetch of `erdosproblems.com/latex/26` exists in any session
log, so no bibliography was recoverable from the site (network blocked);
entries below are honest stubs with missing data omitted rather than guessed.
[Te19] is recovered in full from the upstream formal-conjectures file (log
capture and HEAD clone agree byte-for-byte on the entry).

- [Er95] Erdős, P., Some of my favourite problems in number theory,
  combinatorics, and geometry. Resenhas 1 (1995), 165-186. (Corpus-sourced
  entry, unverified against the site. The corpus is split on this key: a
  minority reading is "Some of my favourite problems in various branches of
  combinatorics", Congressus Numerantium 107 (1995), 167-189; the page
  citations `[Er95, p.165]`/`[Er95, p.166]` recorded for problems 1, 2 and 7
  fall below that paper's first page 167, so the Resenhas reading is
  preferred — see the Problem 17 review for the argument. This problem's own
  cite `[Er95, p.167]` is compatible with both readings.)
- [DaEr51] Davenport, H. and Erdős, P. (1951). (Stub: cited on the page for
  the theorem that every Behrend sequence has divergent reciprocal sum. No
  fuller data recoverable offline. Distinct from [DaEr36] Davenport, H. and
  Erdős, P., On sequences of positive integers, Acta Arithmetica 2 (1936),
  147-151, which the corpus carries for problems 281/487.)
- [Te13] Tenenbaum, G. (2013). (Stub: cited on the page alongside [DaEr51].
  No fuller data recoverable offline.)
- [Te19] Tenenbaum, G., Some of Erdős' unconventional problems in number
  theory, thirty-four years later. arXiv:1908.00488 [math.NT] (2019). (From
  the upstream formal-conjectures reference block.)

Additional thanks (page): Salvatore Mercuri, Imre Ruzsa, and Wouter van
Doorn. 6 forum comments at capture time.
-/

open scoped Classical
open BigOperators Finset

/--
The natural density of a set S ⊆ ℕ is 1, i.e., "almost all" natural numbers
belong to S:  |S ∩ {0,…,N−1}| / N → 1  as N → ∞.
Expressed as: for every ε > 0, for all sufficiently large N,
|S ∩ {0,…,N−1}| ≥ (1 - ε) * N.

(Since the count is trivially ≤ N, this liminf-style lower bound is exactly
density 1; counting {0,…,N−1} rather than {1,…,N} changes the count by at
most 2 and hence not the notion.)
-/
noncomputable def HasDensityOne (S : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) ≥ (1 - ε) * N

/--
The natural density of a set S ⊆ ℕ is **at least c** (in the liminf sense):
for every δ > 0, for all sufficiently large N,
|S ∩ {0,…,N−1}| ≥ (c − δ) * N.

At c = 1 this is exactly `HasDensityOne`. Used for Tenenbaum's weaker
variant ("at least 1 − ε density"); it matches the upstream
formal-conjectures `IsWeaklyBehrend` (stated there via `Set.lowerDensity`).
-/
noncomputable def HasDensityAtLeast (S : Set ℕ) (c : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) ≥ (c - δ) * N

/--
The set of natural numbers that have a divisor in a given set B.
That is, {n ∈ ℕ | ∃ b ∈ B, b ∣ n}.
-/
def HasDivisorIn (B : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ b ∈ B, b ∣ n}

/--
A set B ⊆ ℕ is a **Behrend sequence** if almost all natural numbers
have a divisor in B, i.e., the set {n | ∃ b ∈ B, b ∣ n} has density 1.

(Convention note: the classical definition takes the elements of a Behrend
sequence to exceed 1; this encoding omits that restriction, so `{1}` counts
as Behrend here. In this file the definition is only applied to translates
A + k with k ≥ 1, where the difference is immaterial — see the theorem
docstrings.)
-/
def IsBehrendSeq (B : Set ℕ) : Prop :=
  HasDensityOne (HasDivisorIn B)

/--
The translate of a set A by k: {a + k | a ∈ A}.
-/
def SetTranslate (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, n = a + k}

/--
The set A ⊆ ℕ has divergent reciprocal sum, i.e., ∑_{n ∈ A} 1/n = ∞.
Expressed as: for every bound M, some finite subset of A has reciprocal sum
≥ M. (Same encoding as `DivergentReciprocalSum` in `conjectures/3.lean`;
a possible element 0 contributes 1/0 = 0 in Lean's real division and is
therefore harmless on both sides of every statement below.)
-/
def DivergentReciprocalSum (A : Set ℕ) : Prop :=
  ∀ M : ℝ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧
    M ≤ ∑ n ∈ F, (1 : ℝ) / (n : ℝ)

/--
Erdős Problem #26 [Er95,p.167]:

Let A ⊂ ℕ be infinite. Must there exist some k ≥ 1 such that almost all
integers have a divisor of the form a + k for some a ∈ A?

Equivalently: does there exist k ≥ 1 such that A + k is a Behrend sequence?

Asked by Erdős and Tenenbaum. The answer is **no** — DISPROVED, and the
disproof (for the stronger thick version, see
`erdos_problem_26.variants.thick_counterexample`) is verified in Lean
(Alexeev, using Aristotle; see the module docstring). Ruzsa gave a simple
explicit counterexample (formalized as
`erdos_problem_26.variants.ruzsa_construction`). Davenport and Erdős [DaEr51]
showed that ∑ 1/a = ∞ for every Behrend sequence
(`erdos_problem_26.variants.davenport_erdos`), so taking any infinite A with
∑ 1/a < ∞ (e.g. the powers of 2) immediately gives a counterexample.

Since the question is answered negatively, the theorem asserts the negation
of the universally quantified question (direct-assertion convention of this
pipeline). Note the quantifier ranges over all infinite A ⊆ ℕ including sets
containing 0; this is harmless: removing 0 from a counterexample A leaves a
counterexample (translates only shrink), so the statement is equivalent to
the 1-based reading of the source.
-/
theorem erdos_problem_26 :
    ¬ (∀ (A : Set ℕ), A.Infinite →
      ∃ k : ℕ, 0 < k ∧ IsBehrendSeq (SetTranslate A k)) :=
  sorry

/--
The Davenport–Erdős theorem cited on the problem page [DaEr51] (see also
Tenenbaum [Te13]): every Behrend sequence B has divergent reciprocal sum,
∑_{b ∈ B} 1/b = ∞.

The hypothesis `1 ∉ B` reflects the classical convention that Behrend
sequences consist of integers exceeding 1: without it the statement is false
in this encoding (B = {1} is Behrend as encoded — every integer is divisible
by 1 — yet has reciprocal sum 1). An element 0 is harmless on both sides
(it contributes only n = 0 to the divisor set and 1/0 = 0 to sums), so it is
not excluded.
-/
theorem erdos_problem_26.variants.davenport_erdos
    (B : Set ℕ) (h1 : 1 ∉ B) (hB : IsBehrendSeq B) :
    DivergentReciprocalSum B :=
  sorry

/--
Ruzsa's explicit counterexample from the problem page: "let
A = {n₁ < n₂ < ⋯} where n_l ≡ −(k−1) (mod p_k) for all k ≤ l, where p_k
denotes the k-th prime." Then no translate A + k (k ≥ 1) is Behrend.

Formalized 0-indexed: `a l` is n_{l+1} and `p k` is p_{k+1}, so the source
congruence p_k ∣ n_l + (k−1) (for 1 ≤ k ≤ l) becomes `p k ∣ a l + k` (for
k ≤ l). The statement is generalized from the sequence of *all* primes to any
strictly increasing sequence of primes — the instance p = (2, 3, 5, 7, …)
is the page's construction.

Why this is true (reviewer's argument; the counterexample is page-stated but
the page gives no proof): every a i is a positive multiple of p 0, so
a i ≥ p 0 · (i + 1) ≥ 2(i + 1); for a shift j ≥ 1 every element a i + j with
i ≥ j is divisible by the prime p j, so the multiples of A + j lie in the
union of the multiples of p j and of the j numbers a 0 + j, …, a (j−1) + j,
of upper density at most 1/p j + ∑_{i<j} 1/(2i+2+j) ≤ 2/3 < 1.

The positivity hypothesis `0 < a 0` is necessary and is implicit in the
source's 1-based ℕ: if a 0 = 0 were allowed (0 satisfies every congruence),
then A + 1 would contain 1 and be trivially Behrend, making the statement
false.
-/
theorem erdos_problem_26.variants.ruzsa_construction
    (p : ℕ → ℕ) (hp : StrictMono p) (hpprime : ∀ i, (p i).Prime)
    (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 0 < a 0)
    (hcong : ∀ k l : ℕ, k ≤ l → p k ∣ a l + k) :
    ∀ k : ℕ, 0 < k → ¬ IsBehrendSeq (SetTranslate (Set.range a) k) :=
  sorry

/--
The thick version of the counterexample, confirmed on the problem page: "In
the comments van Doorn explains how Ruzsa's construction above can be
modified to produce a counterexample with ∑ 1/a = ∞." This is the version
whose disproof is Lean-verified (upstream `erdos_26` with `answer(False)`,
"formalized in Lean by Alexeev using Aristotle", formal_proof at
plby/lean-proofs `Erdos26.lean`): there is an infinite A with divergent
reciprocal sum none of whose translates A + k (k ≥ 1) is Behrend. (This is
the interesting direction — for A with convergent reciprocal sum the
conclusion already follows from
`erdos_problem_26.variants.davenport_erdos`.)
-/
theorem erdos_problem_26.variants.thick_counterexample :
    ∃ A : Set ℕ, A.Infinite ∧ DivergentReciprocalSum A ∧
      ∀ k : ℕ, 0 < k → ¬ IsBehrendSeq (SetTranslate A k) :=
  sorry

/--
Tenenbaum's weaker variant, stated on the problem page: for every ε > 0 is
there some k = k(ε) ≥ 1 such that at least 1 − ε density of all integers
have a divisor of the form a + k for some a ∈ A? (Quantified over thick
infinite A, matching the upstream encoding — for A with convergent
reciprocal sum even the weak conclusion fails for large k.)

Status: the page capture (accessed 2026-03-05) records this as *still open*;
the upstream formal-conjectures file at HEAD (2026-08-16, fresher) marks it
solved with `answer(False)` — "The DeepMind prover agent has found a formal
disproof of this statement" (formal_proof link into the
mo271/formal-conjectures fork). This theorem asserts that negative
resolution: it is the negation of the question's universal statement, and is
implied by upstream's disproved statement (which allows even k = 0 and is
stated via `Set.lowerDensity`, equivalent to `HasDensityAtLeast (1 − ε)`
here). If upstream's status is in error, this statement is open rather than
false, since it claims exactly the negative answer.
-/
theorem erdos_problem_26.variants.tenenbaum_disproof :
    ¬ (∀ A : Set ℕ, A.Infinite → DivergentReciprocalSum A →
      ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, 0 < k ∧
        HasDensityAtLeast (HasDivisorIn (SetTranslate A k)) (1 - ε)) :=
  sorry
