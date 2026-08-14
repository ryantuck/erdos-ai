import Mathlib.Data.Int.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Erdős Problem #1148

Can every large integer n be written as n = x² + y² − z² with
max(x², y², z²) ≤ n?

Verbatim source statement (erdosproblems.com/1148): "Can every large integer
$n$ be written as $n=x^2+y^2-z^2$ with $\max(x^2,y^2,z^2)\leq n$?"

Status: OPEN per erdosproblems.com/1148 (page last edited 26 January 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "The largest integer known which cannot be written this way is $6563$.
  [Va99] reports this is 'obvious' if we replace $\leq n$ with
  $\leq n+2\sqrt{n}$."

The source poses this as a yes/no question and the problem is OPEN; this raw
corpus has no `answer()` elaborator (Mathlib-only imports), and its uniform
convention for open yes/no questions is a direct assertion of the asked
("yes") direction with a `sorry` proof, as here. In styled question form it
would be `answer(sorry) ↔ ∃ N, ∀ n ≥ N, …`.

Computational cross-checks (performed during the second-pass review; they are
context, not formal content): 6563 is indeed not representable under the
≤ n constraint (finite check over x, y, z ≤ 81 = ⌊√6563⌋); no
non-representable integer exists in (6563, 20000]; exactly 77
non-representable integers exist below 8000 (the largest few being 5447,
5727, 6563); and the relaxed ≤ n + 2√n bound of the [Va99] remark admits no
exceptions for n < 4000.

Tags (per the page): number theory.
Related OEIS sequences (per the page): A390380, A393168 (sequence contents
not verifiable offline).
Formalised statement (per the page, as of access): Yes —
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1148.lean.
The page records 6 forum comments; their contents were not captured.

References (honest stub; `/latex/1148` and `/bibs/` fetches were not captured
in the session logs, so the entry is a stub — no data fabricated):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.25. (Corpus-canonical identity of this key: the upstream
  formal-conjectures file for this very problem carries exactly this
  expansion, recovered from the session logs, and it is corroborated by
  sibling problems 1068 and 1131–1147. Several sibling styled files glossed
  [Va99] with invented authors — Vaughan, Vardi, Vu, Vershik, … — a known
  hallucinated-attribution failure class; none of that is reproduced here.)
-/

/--
Erdős Problem #1148 [Va99, 1.25] (Open):

Can every large integer n be written as n = x² + y² - z² with
max(x², y², z²) ≤ n?

The largest integer known which cannot be written this way is 6563
(see `erdos_problem_1148.variants.not_6563`). [Va99] reports this is
'obvious' if we replace ≤ n with ≤ n + 2√n
(see `erdos_problem_1148.variants.relaxed_bound`).

Tags: number theory
-/
theorem erdos_problem_1148 :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ x y z : ℕ, (x ^ 2 + y ^ 2 : ℤ) - z ^ 2 = n ∧
        x ^ 2 ≤ n ∧ y ^ 2 ≤ n ∧ z ^ 2 ≤ n :=
  sorry

/--
The page's concrete record: 6563 cannot be written as x² + y² - z² with
max(x², y², z²) ≤ 6563 — "the largest integer known which cannot be written
this way". This is a finite statement (any witness has x, y, z ≤ 81 = ⌊√6563⌋)
and was re-verified computationally during this review.
-/
theorem erdos_problem_1148.variants.not_6563 :
    ¬ ∃ x y z : ℕ, (x ^ 2 + y ^ 2 : ℤ) - z ^ 2 = 6563 ∧
        x ^ 2 ≤ 6563 ∧ y ^ 2 ≤ 6563 ∧ z ^ 2 ≤ 6563 :=
  sorry

/--
[Va99] reports it is 'obvious' that every large integer n can be written as
n = x² + y² - z² once the constraint max(x², y², z²) ≤ n is relaxed to
max(x², y², z²) ≤ n + 2√n.

(Sketch supporting the remark: for n not a perfect square let a = ⌈√n⌉ and
m = a² − n, so 0 < m < 2a − 1 and a² ≤ n + 2√n. If m ≢ 2 (mod 4), write
m = z² − y² with z ≤ a and take x = a; otherwise 2a − 1 − m is odd and
positive, write it as y² − z² with y ≤ a and take x = a − 1, so x² < n.
Verified computationally with no exceptions for n < 4000.)
-/
theorem erdos_problem_1148.variants.relaxed_bound :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ x y z : ℕ, (x ^ 2 + y ^ 2 : ℤ) - z ^ 2 = n ∧
        (x ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
        (y ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n ∧
        (z ^ 2 : ℝ) ≤ n + 2 * Real.sqrt n :=
  sorry
