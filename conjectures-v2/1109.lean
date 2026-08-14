import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Pointwise Real

/-!
# Erdős Problem #1109

Let f(N) be the size of the largest subset A ⊆ {1, ..., N} such that every
n ∈ A + A is squarefree. Estimate f(N). In particular, is it true that
f(N) ≤ N^{o(1)}, or even f(N) ≤ (log N)^{O(1)}?

**Status: OPEN** (erdosproblems.com banner; page edition 03 December 2025,
accessed 2026-02-23).

First studied by Erdős and Sárközy [ErSa87], who proved
  log N ≪ f(N) ≪ N^{3/4} · log N,
and guessed the lower bound is nearer the truth. Sárközy [Sa92c] extended
this to consider the case of A + B and also looking for sumsets which are
k-power-free. Gyarmati [Gy01] gave an alternative proof of f(N) ≫ log N,
and also gave new bounds for the case of A + B. Konyagin [Ko04] improved
this to
  (log log N) · (log N)² ≪ f(N) ≪ N^{11/15 + o(1)}.

The infinite analogue of this problem is #1103 (`conjectures/1103.lean`):
in particular, upper bounds for this f(N) directly imply lower bounds for
the size of the a_j considered there.

## References

Bibliographic details below come from the original pipeline's fetch of
erdosproblems.com/latex/1109, preserved in the session logs only as the
fetch agent's structured extraction (not raw HTML). Journal volume numbers
were absent from that extraction and are not invented here. The [Ko04]
entry is corroborated verbatim by the sibling file
`deepmind/deepmind/1103.lean`; the other three entries are uncorroborated
and their full verification is DEFERRED pending network access.

- [ErSa87] Erdős, P. and Sárközy, A., _On divisibility properties of
  integers of the form a + a'_. Acta Math. Hungar. (1987), 117–122.
- [Sa92c] Sárközy, G. N., _On a problem of P. Erdős_. Acta Math. Hungar.
  (1992), 271–282. (The page's remark says only "Sárközy"; the "G. N."
  initials are as extracted and remain DEFERRED for verification.)
- [Gy01] Gyarmati, K., _On divisibility properties of integers of the form
  ab + 1_. Period. Math. Hungar. (2001), 71–79.
- [Ko04] Konyagin, S. V., _Problems of the set of square-free numbers_.
  Izv. Ross. Akad. Nauk Ser. Mat. (2004), 63–90.

https://www.erdosproblems.com/1109
Tags: number theory
Related OEIS sequences: A392164, A392165
-/

/--
Erdős Problem #1109, stronger question [ErSa87]:

Let f(N) be the size of the largest subset A ⊆ {1, ..., N} such that every
n ∈ A + A is squarefree. Is it true that f(N) ≤ (log N)^{O(1)}?

This question is OPEN; the statement below asserts the conjectured
affirmative direction (Erdős and Sárközy guessed their lower bound
log N ≪ f(N) was nearer the truth than their upper bound), following this
corpus's convention for open yes/no questions. The weaker sub-question
f(N) ≤ N^{o(1)} asked by the same problem is
`erdos_problem_1109_subpolynomial` below.

Formalized as: there exist constants C > 0 and k > 0 such that for all
sufficiently large N, every subset A ⊆ {1, ..., N} whose sumset A + A is
entirely squarefree satisfies |A| ≤ C · (log N)^k. Restricting the exponent
k to positive naturals loses no generality: a real exponent bound K may be
raised to ⌈K⌉ once log N ≥ 1. The "sufficiently large N" is necessary: at
N = 1 the admissible set A = {1} (with A + A = {2} squarefree) has
card 1 > C · (log 1)^k = 0 for every C and k.

First studied by Erdős and Sárközy [ErSa87], who proved
  log N ≪ f(N) ≪ N^{3/4} · log N.
Konyagin [Ko04] improved this to
  (log log N) · (log N)² ≪ f(N) ≪ N^{11/15 + o(1)}.
-/
theorem erdos_problem_1109_conjecture :
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℕ, 0 < k ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ C * (log N) ^ k :=
  sorry

/--
Erdős Problem #1109, weaker question [ErSa87] — the other half of the
source's "is it true that f(N) ≤ N^{o(1)}, or even f(N) ≤ (log N)^{O(1)}?",
missing from the first pass:

Is it true that f(N) ≤ N^{o(1)}?

This question is OPEN; the statement asserts the conjectured affirmative
direction, per the corpus convention. It is implied by (but does not imply)
`erdos_problem_1109_conjecture`, since polylogarithmic growth is
subpolynomial; it may be the more tractable of the two.

f(N) ≤ N^{o(1)} means: for every ε > 0, f(N) ≤ N^ε for all sufficiently
large N. Since this file does not import rpow, N^ε is written as
exp(ε · log N), which equals N^ε for every N ≥ 1 (the ∃ N₀ makes the
N = 0 discrepancy irrelevant).
-/
theorem erdos_problem_1109_subpolynomial :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ exp (ε * log N) :=
  sorry

/--
Variant (Erdős–Sárközy [ErSa87], solved; alternative proof by Gyarmati
[Gy01]): f(N) ≫ log N — for some c > 0 and all large N there is a subset
of {1, ..., N} of size at least c · log N whose sumset is entirely
squarefree. Superseded by `erdos_problem_1109_konyagin_lower`.
-/
theorem erdos_problem_1109_erdos_sarkozy_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∀ n ∈ A + A, Squarefree n) ∧
      c * log N ≤ (A.card : ℝ) :=
  sorry

/--
Variant (Konyagin [Ko04], solved): (log log N) · (log N)² ≪ f(N) — for
some c > 0 and all large N there is a subset of {1, ..., N} of size at
least c · (log log N) · (log N)² whose sumset is entirely squarefree.
This improves the [ErSa87] lower bound f(N) ≫ log N.
-/
theorem erdos_problem_1109_konyagin_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∃ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      (∀ n ∈ A + A, Squarefree n) ∧
      c * (log (log N) * (log N) ^ 2) ≤ (A.card : ℝ) :=
  sorry

/--
Variant (Konyagin [Ko04], solved): f(N) ≪ N^{11/15 + o(1)}, i.e. for every
ε > 0 and all sufficiently large N, every subset of {1, ..., N} with
entirely squarefree sumset has size at most N^{11/15 + ε}. As in
`erdos_problem_1109_subpolynomial`, N^x is written exp(x · log N).

This improves Erdős–Sárközy's upper bound f(N) ≪ N^{3/4} · log N [ErSa87]
(11/15 < 3/4); the superseded bound is recorded in the module docstring and
not separately formalized.
-/
theorem erdos_problem_1109_konyagin_upper :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ exp ((11 / 15 + ε) * log N) :=
  sorry
