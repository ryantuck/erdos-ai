-- [AI - Claude Sonnet 5.5]: Erdős Problem 123 — second-pass formalization
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

/-!
# Erdős Problem #123: d-Complete Sequences of Smooth Numbers

*Source:* [erdosproblems.com/123](https://www.erdosproblems.com/123) (status **OPEN** when
captured: "This is open, and cannot be resolved with a finite computation."; prize \$250; captured
2026-02-20 and 2026-03-05 as the tidied problem box; **proved** since, see below).
[Er92b] [ErLe96] [Er97] [Er97e]

Let $a,b,c\geq 1$ be three integers which are pairwise coprime. Is every large integer the sum
of distinct integers of the form $a^kb^lc^m$ ($k,l,m\geq 0$), none of which divide any other?

Remarks recorded on the page:
* A sequence is said to be $d$-complete if every large integer is the sum of distinct integers
  from the sequence, none of which divide any other. This particular case of $d$-completeness
  was conjectured by Erdős and Lewin [ErLe96], who (among other related results) prove this
  when $a=3$, $b=5$, and $c=7$.
* As a partial record of progress so far, the sequence $\{a^kb^lc^m\}$ is known to be
  $d$-complete when:
  * $a=3$, $b=5$, $c=7$ (Erdős and Lewin [ErLe96]);
  * $a=2$, $b=5$, $c\in \{7,11,13,17,19\}$ (Erdős and Lewin [ErLe96]);
  * $a=2$, $b=5$, $c\in \{9,21,23,27,29,31\}$, and more generally $a=2$, $b=5$, and any $c>6$
    with $(c,10)=1$ such that there exists $N$ where every integer in $(N,25cN)$ is the sum of
    distinct elements of $\{2^k3^lc^m\}$, none of which divide any other (Ma and Chen
    [MaCh16]);
  * $a=2$, $b=5$, $3\leq c\leq 87$ with $(c,10)=1$, or $a=2$, $b=7$, $3\leq c\leq 33$ with
    $(c,14)=1$, or $a=3$, $b=5$, $2\leq c\leq 14$ with $(c,15)=1$ (Chen and Yu [ChYu23b]).
* In [Er92b] Erdős makes the stronger conjecture (for $a=2$, $b=3$, and $c=5$) that, for any
  $\epsilon>0$, all large integers $n$ can be written as the sum of distinct integers
  $b_1<\cdots <b_t$ of the form $2^k3^l5^m$ where $b_t<(1+\epsilon)b_1$.
* See also Problem #845, and #1110 for the case of two powers.

Tags: number theory.

**Status after capture.** The site owner's mirror (`teorth/erdosproblems`) changed this problem
from `open` to `proved (Lean)` in commit `8cbad71` (2026-07-17, "status of 123"). Upstream
`erdos_123` is `answer(True)`, credits GPT 5.6 (prompted by Snyder), says it was formalized in
Lean by Alexeev, and links a formal proof. This second-pass review has not checked that result.
The first pass asserts the asked ("yes") direction, which is the proved direction.

**The range of $a,b,c$.** The page says $a,b,c\ge1$, and the first pass assumed
`1 ≤ a`, `1 ≤ b`, `1 ≤ c`. That admits degenerate triples:
* For $a=b=c=1$ the set is $\{1\}$, and no integer $n\ge2$ is a sum of distinct elements of it.
  So the first pass's theorem is false. This is `erdos_problem_123.variants.first_pass_false`.
* For $a=1$ and $b,c\ge2$ coprime the set is the two-power set $\{b^lc^m\}$. By Erdős and Lewin
  [ErLe96], as recorded on the page of Problem #1110, such a set is $d$-complete only when
  $\{b,c\}=\{2,3\}$. So the first pass's theorem also fails at $(1,3,5)$, $(1,2,5)$ and
  $(1,5,7)$, among others. A brute-force search for $\{3^k5^l\}$ finds $726$ non-representable
  $n\le900$, including $892$ to $898$ and $900$. See `erdos_problem_123.variants.a_one_not_dcomplete`.

The intended range is $a,b,c\ge2$, as in upstream. Pairwise coprimality then also makes them
distinct. v2 uses `2 ≤ a`, `2 ≤ b`, `2 ≤ c`.

**Encoding.** "Distinct integers" are the elements of a `Finset`. "None of which divide any
other" is `DivisibilityAntichain`. "Every large integer" is the `∃ N, ∀ n ≥ N` form. The
threshold matters. For $(3,5,7)$ a brute-force search finds non-representable
$n\le200$ at $2,4,6,11,13,17,18,19,20,23,29,33,37,43,51,92,100,148,185$, while
$(2,3,5)$ represents every $n\le200$.

## References

* [Er92b] Erdős, P., _Some of my favourite problems in various branches of combinatorics_.
  Matematiche (Catania) (1992), 231–240.
* [ErLe96] Erdős, P. and Lewin, M., _$d$-complete sequences of integers_. Math. Comp. (1996),
  837–840.
* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.
* [MaCh16] Ma, M.-M. and Chen, Y.-G., _On $d$-complete sequences of integers_. J. Number Theory
  (2016), 1–12.
* [ChYu23b] Chen, Y.-G. and Yu, W.-X., _On $d$-complete sequences of integers, II_. Acta Arith.
  (2023), 161–181.

(Provenance: no `/latex/123` fetch exists in the session logs. All six entries are from upstream
`123.lean`. [Er92b] and [ErLe96]'s title also appear in sibling `/latex` extractions, which
agree. On the page, the set in Ma and Chen's criterion reads $\{2^k3^lc^m\}$. The bound $25cN$
suggests that $3$ is a typo for $b=5$. The criterion is not formalized.)
-/

/-- The set of numbers of the form a^k * b^l * c^m for nonneg exponents. -/
def smoothNumbers (a b c : ℕ) : Set ℕ :=
  { n | ∃ k l m : ℕ, n = a ^ k * b ^ l * c ^ m }

/-- A finite set of natural numbers is an antichain under divisibility:
    no element divides any other distinct element. -/
def DivisibilityAntichain (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ∣ y → x = y

/-- A set S ⊆ ℕ is d-complete if every sufficiently large natural number
    can be written as the sum of distinct elements of S, no one of which
    divides another. -/
def IsDComplete (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ s : Finset ℕ, ↑s ⊆ S ∧ DivisibilityAntichain s ∧ s.sum id = n

/--
Erdős Problem #123 [Er92b, ErLe96, Er97, Er97e] — OPEN when captured ($250); recorded as PROVED
since 2026-07-17 (see the module docstring).

Let a, b, c ≥ 2 be three integers which are pairwise coprime. Is every
sufficiently large integer the sum of distinct integers of the form
a^k * b^l * c^m (k, l, m ≥ 0), none of which divide any other?

Equivalently, is the set {a^k * b^l * c^m : k, l, m ≥ 0} always d-complete
when a, b, c are pairwise coprime?

The range is a, b, c ≥ 2. The first pass allowed 1 ≤ a, b, c, but then a = b = c = 1 gives the
set {1}, and the statement is false (see `erdos_problem_123.variants.first_pass_false`).

Erdős and Lewin proved the case a=3, b=5, c=7, along with several cases
with a=2, b=5. Further cases have been verified by Ma–Chen and Chen–Yu.
-/
theorem erdos_problem_123
    (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    IsDComplete (smoothNumbers a b c) :=
  sorry

/--
The first-pass statement, with `1 ≤ a, b, c`, is false (PROVED): at a = b = c = 1 the set is {1},
so no n ≥ 2 is a sum of distinct elements of it.
-/
theorem erdos_problem_123.variants.first_pass_false :
    ¬ (∀ a b c : ℕ, 1 ≤ a → 1 ≤ b → 1 ≤ c →
        Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c →
        IsDComplete (smoothNumbers a b c)) := by
  intro h
  obtain ⟨N, hN⟩ := h 1 1 1 le_rfl le_rfl le_rfl
    (Nat.coprime_one_left 1) (Nat.coprime_one_left 1) (Nat.coprime_one_left 1)
  obtain ⟨s, hs, -, hsum⟩ := hN (N + 2) (Nat.le_add_right N 2)
  have hsub : s ⊆ ({1} : Finset ℕ) := by
    intro x hx
    obtain ⟨k, l, m, hx'⟩ := hs (Finset.mem_coe.mpr hx)
    simp [hx']
  have hle : s.sum id ≤ ({1} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub
  rw [hsum] at hle
  simp at hle

/--
A two-power set is not d-complete (PROVED; Erdős and Lewin [ErLe96], as recorded on the page of
Problem #1110, not on this page): {3^k 5^l} has infinitely many non-representable numbers. So the
first-pass statement fails at (a, b, c) = (1, 3, 5) as well as at (1, 1, 1). More generally,
{b^l c^m} is d-complete for coprime b, c ≥ 2 only when {b, c} = {2, 3}.
-/
theorem erdos_problem_123.variants.a_one_not_dcomplete :
    ¬ IsDComplete (smoothNumbers 1 3 5) :=
  sorry

/--
Erdős and Lewin [ErLe96] (PROVED): the set {3^k 5^l 7^m} is d-complete.
-/
theorem erdos_problem_123.variants.erdos_lewin_3_5_7 :
    IsDComplete (smoothNumbers 3 5 7) :=
  sorry

/--
Erdős and Lewin [ErLe96] (PROVED): {2^k 5^l c^m} is d-complete for c ∈ {7, 11, 13, 17, 19}.
-/
theorem erdos_problem_123.variants.erdos_lewin_2_5 :
    ∀ c ∈ ({7, 11, 13, 17, 19} : Finset ℕ), IsDComplete (smoothNumbers 2 5 c) :=
  sorry

/--
Ma and Chen [MaCh16] (PROVED): {2^k 5^l c^m} is d-complete for c ∈ {9, 21, 23, 27, 29, 31}.
-/
theorem erdos_problem_123.variants.ma_chen_2_5 :
    ∀ c ∈ ({9, 21, 23, 27, 29, 31} : Finset ℕ), IsDComplete (smoothNumbers 2 5 c) :=
  sorry

/--
Chen and Yu [ChYu23b] (PROVED): d-completeness for a = 2, b = 5, 3 ≤ c ≤ 87 with (c, 10) = 1;
for a = 2, b = 7, 3 ≤ c ≤ 33 with (c, 14) = 1; and for a = 3, b = 5, 2 ≤ c ≤ 14 with (c, 15) = 1.
-/
theorem erdos_problem_123.variants.chen_yu :
    (∀ c : ℕ, 3 ≤ c → c ≤ 87 → Nat.Coprime c 10 → IsDComplete (smoothNumbers 2 5 c)) ∧
    (∀ c : ℕ, 3 ≤ c → c ≤ 33 → Nat.Coprime c 14 → IsDComplete (smoothNumbers 2 7 c)) ∧
    (∀ c : ℕ, 2 ≤ c → c ≤ 14 → Nat.Coprime c 15 → IsDComplete (smoothNumbers 3 5 c)) :=
  sorry

/--
Erdős's stronger conjecture [Er92b] (OPEN; asserted in the conjectured direction): for any
ε > 0, all large n are sums of distinct elements of {2^k 3^l 5^m} whose largest is below
(1 + ε) times the smallest.
-/
theorem erdos_problem_123.variants.snug :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (s : Finset ℕ) (hs : s.Nonempty), (↑s : Set ℕ) ⊆ smoothNumbers 2 3 5 ∧
        s.sum id = n ∧ ∀ a ∈ s, (a : ℝ) < (1 + ε) * ((s.min' hs : ℕ) : ℝ) :=
  sorry
