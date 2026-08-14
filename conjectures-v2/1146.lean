import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #1146

We say that A ⊆ ℕ is an essential component if d_s(A+B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density.

Is B = {2^m 3^n : m, n ≥ 0} an essential component?

Verbatim source statement (erdosproblems.com/1146): "We say that $A\subset
\mathbb{N}$ is an essential component if $d_s(A+B)>d_s(B)$ for every
$B\subset \mathbb{N}$ with $0<d_s(B)<1$ where $d_s$ is the Schnirelmann
density. Is $B=\{2^m3^n : m,n\geq 0\}$ an essential component?"

Status: OPEN per erdosproblems.com/1146 (page last edited 23 January 2026,
accessed 2026-02-23) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "In [Ru99] Ruzsa states 'The simplest set with a chance to be an essential
  component is the collection of numbers in the form $2^m3^n$ and Erdős often
  asked whether it is an essential component or not; I do not even have a
  plausible guess.'"
* "See also [37]." (Erdős Problem #37, formalized in `conjectures/37.lean`:
  Ruzsa [Ru87] proved that lacunary sets cannot be essential components; the
  3-smooth numbers are not lacunary, which is why they are "the simplest set
  with a chance".)

Encoding note (fix relative to `conjectures/1146.lean`): the sumset in the
essential-component condition adjoins 0 to both sets,
C = (A ∪ {0}) + (B ∪ {0}) = A ∪ B ∪ (A + B) ∪ {0}, the classical convention
of the Schnirelmann-density literature (Halberstam–Roth, *Sequences*, where
sets in Schnirelmann addition are taken to contain 0; likewise the classical
essential components — the squares with 0², Khinchin; bases of order k,
Erdős — all contain 0, and the sibling formalization `conjectures/35.lean`
of the related Erdős–Plünnecke density inequality explicitly hypothesizes
0 ∈ B). Under the *strict* sumset {a + b : a ∈ A, b ∈ B} used by the first
pass, the statement is trivially false for every A with 0 ∉ A — in
particular for the 3-smooth numbers: taking B₀ = ℕ \ {0, 2} one has
d_s(B₀) = 1/2 ∈ (0,1), while every element of A + B₀ is ≥ 1 + 1 = 2, so
1 ∉ A + B₀, the n = 1 term of the defining infimum is 0, and hence
d_s(A + B₀) = 0 < 1/2 — refuting the literal statement for a degenerate
reason foreign to the problem (an open question would be encoded as a
provably false assertion). With 0 adjoined, C ⊇ B, so d_s(C) ≥ d_s(B)
always holds and the question is exactly the intended one: does adding the
3-smooth numbers *strictly* increase every intermediate Schnirelmann
density? (The same strict-sumset issue is present in the archived styled
copy `deepmind/deepmind/1146.lean` and in the upstream formal-conjectures
version recovered from the session logs, where the pointwise `A + B` is
also the strict sumset.)

The source poses this as a yes/no question and the problem is OPEN; this raw
corpus has no `answer()` elaborator (Mathlib-only imports), and its uniform
convention for open yes/no questions is a direct assertion of the asked
("yes") direction with a `sorry` proof, as here. In styled question form it
would be `answer(sorry) ↔ IsEssentialComponent1146 smoothNumbers23`.

Reuse note (deferred, compile-dependent): Mathlib pinned at v4.28.0 already
provides `schnirelmannDensity` (`Mathlib.Combinatorics.Schnirelmann`,
authors Dillies–Mehta–Sertbas), mathematically identical to the local
definition (`Finset.Ioc 0 n` = {1, …, n} there vs `Finset.Icc 1 n` here);
the local `sumset1146` duplicates Mathlib's pointwise `Set` addition
(`A + B` under `open Pointwise`); and `smoothNumbers23` is extensionally
equal to Mathlib's `Nat.smoothNumbers 4` (both contain 1 and exclude 0).
The local definitions are kept because swapping them cannot be
compile-verified in this container.

Tags (per the page): number theory.
Related OEIS sequences (per the page): possible, none listed.
Formalised statement (per the page, as of access): No.

Reference: [Va99, 1.19]
https://www.erdosproblems.com/1146

References (stubs; `/latex/1146` and `/bibs/` were not captured in the
session logs, so entries are honest stubs — no data fabricated):
[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.19. (This identification follows the site's uniform bibliography for
  the key, corroborated by sibling problems 1068 and 1137–1145. Note: the
  gloss of `[Va99]` as "Ruzsa, I. Z., *Sumsets and structure*, Combinatorial
  Number Theory and Additive Group Theory (1999)" in the archived styled
  copy `deepmind/deepmind/1146.lean` is a hallucination for this key — that
  Ruzsa survey exists but appeared in the CRM Barcelona volume published in
  2009, and it is not the site's [Va99].)
[Ru99] Ruzsa, I. Z., _Erdős and the integers_. Journal of Number Theory
  (1999), 115-163. (Journal/year/pages as recorded in the archived styled
  copy; volume number not recoverable offline and therefore omitted.)
-/

open Classical

noncomputable section

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n

The infimum is taken in ℝ over the nonempty, 0-bounded-below family indexed
by ℕ+, so it is a genuine infimum with value in [0, 1]; membership of 0 in A
is invisible to it. (Mathlib v4.28.0 has an identical `schnirelmannDensity`
in `Mathlib.Combinatorics.Schnirelmann`; kept local pending a compile pass.)
-/
noncomputable def schnirelmannDensity1146 (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The (strict) sumset A + B = {a + b | a ∈ A, b ∈ B} for sets of natural
numbers. (Duplicates Mathlib's pointwise `A + B`; kept local pending a
compile pass.)
-/
def sumset1146 (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
The Schnirelmann sum of A and B: the sumset formed after adjoining 0 to both
sets,
  (A ∪ {0}) + (B ∪ {0}) = A ∪ B ∪ (A + B) ∪ {0}.

This is the classical convention of the Schnirelmann-density literature
(Halberstam–Roth, *Sequences*), under which the sum always contains both
summand sets. It is required for the essential-component condition to be
non-degenerate: with the strict sumset, any A with 0 ∉ A would fail to be an
essential component for the trivial reason that 1 ∉ A + B whenever 0 ∉ B,
forcing d_s(A + B) = 0 (see the module docstring for the counterexample).
-/
def schnirelmannSum1146 (A B : Set ℕ) : Set ℕ :=
  sumset1146 (A ∪ {0}) (B ∪ {0})

/--
A set A ⊆ ℕ is an essential component if d_s(A + B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density and the
sum A + B adjoins 0 to both sets (classical convention; see
`schnirelmannSum1146`). Since the sum then contains B, d_s(A + B) ≥ d_s(B)
holds automatically and the condition asks for *strict* increase.

Note: 0 < d_s(B) forces 1 ∈ B (the n = 1 term of the infimum is
|B ∩ {1}|/1), but places no constraint on 0 ∈ B — which is why the 0-adjoined
sum, rather than the strict sumset, is the faithful encoding.
-/
def IsEssentialComponent1146 (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity1146 B → schnirelmannDensity1146 B < 1 →
    schnirelmannDensity1146 (schnirelmannSum1146 A B) > schnirelmannDensity1146 B

/--
The set of 3-smooth numbers: {2^m * 3^n | m, n ≥ 0}.

Contains 1 (m = n = 0) and not 0 (2^m * 3^n ≥ 1). Extensionally equal to
Mathlib's `Nat.smoothNumbers 4` (positive naturals all of whose prime
factors are < 4).
-/
def smoothNumbers23 : Set ℕ :=
  {k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n}

/--
Erdős Problem #1146 [Va99, 1.19] (Open):
Is the set B = {2^m * 3^n : m, n ≥ 0} an essential component?

A set A ⊆ ℕ is an essential component if d_s(A + B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density and the
sum adjoins 0 to both sets (classical convention; see
`schnirelmannSum1146` and the module docstring for why the strict sumset
would make this statement trivially false).

In [Ru99] Ruzsa states: "The simplest set with a chance to be an essential
component is the collection of numbers in the form 2^m 3^n and Erdős often
asked whether it is an essential component or not; I do not even have a
plausible guess."

The problem is OPEN; per this corpus's convention the asked ("yes")
direction is stated as a direct assertion with a `sorry` proof. In styled
question form it would be
`answer(sorry) ↔ IsEssentialComponent1146 smoothNumbers23`.
See also Erdős Problem #37 (`conjectures/37.lean`).
-/
theorem erdos_problem_1146 : IsEssentialComponent1146 smoothNumbers23 :=
  sorry

end
