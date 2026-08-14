import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset Classical

noncomputable section

namespace Erdos1110

/-!
# Erdős Problem #1110

Let p > q ≥ 2 be two coprime integers. We call n *representable* if it is
the sum of integers of the form p^k q^l, none of which divide each other.

If {p,q} ≠ {2,3} then what can be said about the density of
non-representable numbers? Are there infinitely many coprime
non-representable numbers?

**Status: OPEN** (erdosproblems.com banner; page edition 22 January 2026,
accessed 2026-02-23). The first question ("what can be said about the
density?") is open-ended and is not formalized directly; the partial
density results of Yu and Chen are formalized as variants below. The
second question is formalized as `erdos_problem_1110`.

A problem of Erdős and Lewin [ErLe96], who proved that there are finitely
many non-representable numbers if and only if {p,q} = {2,3}
(`erdos_problem_1110_erdos_lewin`).

Indeed, in [Er92b] Erdős wrote "last year I made the following silly
conjecture": every integer n can be written as the sum of distinct
integers of the form 2^k 3^l, none of which divide any other. He wrote
"I mistakenly thought that this was a nice and difficult conjecture but
Jansen and several others found a simple proof by induction." The simple
proof: one shows the representation always exists and moreover that if n
is even all summands can be taken even — if n = 2m apply the inductive
hypothesis to m; if n is odd, subtract the largest power of 3 that is
≤ n and apply the inductive hypothesis to the (even) remainder
(`erdos_problem_1110_jansen`).

Yu and Chen [YuCh22] prove that the set of representable numbers has
density zero whenever q > 3, or q = 3 and p > 6, or q = 2 and p > 10
(`erdos_problem_1110_yu_chen_density`). They also prove that there are
infinitely many coprime non-representable numbers if q > 3, or q = 3 and
p ≠ 5, or q = 2 and p ∉ {3,5,9} (`erdos_problem_1110_yu_chen_infinite`).
The main conjecture therefore remains open precisely for
(p,q) ∈ {(5,2), (9,2), (5,3)}.

Erdős and Lewin [ErLe96] also asked whether all large integers n can be
written as a sum of 2^k 3^l, none of which divide another, each of which
is > f(n) for some f(n) → ∞. Let f(n) be the fastest growing such f(n).
Yu and Chen [YuCh22] proved n/(log n)^{log_2 3} ≪ f(n) ≪ n/log n, and
Yang and Zhao [YaZh25] improved the lower bound to f(n) ≫ n/log n. The
qualitative (affirmative) answer is `erdos_problem_1110_erdos_lewin_growth`;
the quantitative bounds are not formalized (they would need real
logarithms, a construct not present in this file).

The case of three powers is the subject of problem [123],
see also [845] for more on the case {p,q} = {2,3}. Problem [246]
addresses the topic without the non-divisibility condition.

## References

Bibliographic details below come from the original pipeline's fetch of
erdosproblems.com/latex/1110, preserved in the session logs only as the
fetch agent's structured extraction (not raw HTML). Journal volume
numbers were absent from that extraction and are not invented here;
their verification is DEFERRED pending network access.

- [ErLe96] Erdős, P. and Lewin, M., _d-complete sequences of integers_.
  Math. Comp. (1996), 837-840.
- [Er92b] Erdős, P., _Some of my favourite problems in various branches
  of combinatorics_. Matematiche (Catania) (1992), 231-240.
- [YuCh22] Yu, W.-X. and Chen, Y.-G., _On a conjecture of Erdős and
  Lewin_. J. Number Theory (2022), 763-778.
- [YaZh25] Yang, Q.-H. and Zhao, L., _A conjecture of Yu and Chen
  related to the Erdős-Lewin theorem_. Acta Arith. (2025), 277-286.

https://www.erdosproblems.com/1110
Tags: number theory
Related OEIS sequences: none listed (the page marks them "Possible")
-/

/-- A natural number m is a (p,q)-power if m = p^a * q^b for some
    a, b ≥ 0. (For p, q ≥ 1 — in particular under this file's standing
    hypotheses p > q ≥ 2 — every (p,q)-power is automatically positive,
    so m = 0 never qualifies.) -/
def IsPQPower (p q m : ℕ) : Prop :=
  ∃ a b : ℕ, m = p ^ a * q ^ b

/-- A finite set of natural numbers is an antichain under divisibility:
    no element divides a distinct element. (Equivalent to Mathlib's
    `IsAntichain (· ∣ ·) (S : Set ℕ)`; kept local so this file depends
    only on its listed imports.) -/
def IsDivisibilityAntichain (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ∣ y → x = y

/-- A natural number n is (p,q)-representable if n equals the sum of a nonempty finite set
    of numbers of the form p^a * q^b, where no element divides another.

    The `Finset` encoding makes the summands distinct, but this loses no
    generality: a repeated summand would divide itself, violating the
    antichain condition. `S.Nonempty` keeps the empty sum from making
    0 vacuously representable. -/
def IsRepresentable (p q n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.Nonempty ∧
    (∀ m ∈ S, IsPQPower p q m) ∧
    IsDivisibilityAntichain S ∧
    S.sum id = n

/--
Erdős Problem #1110 [ErLe96]:

For coprime integers p > q ≥ 2 with {p,q} ≠ {2,3}, are there infinitely
many non-representable numbers that are coprime to p·q?

This question is OPEN; the statement below asserts the conjectured
affirmative direction, following this corpus's convention for open
yes/no questions. Yu and Chen [YuCh22] proved it for every parameter
pair except (p,q) ∈ {(5,2), (9,2), (5,3)}
(`erdos_problem_1110_yu_chen_infinite`), which remain open.

Since p > q ≥ 2 and p, q are coprime, the only excluded case is p = 3, q = 2.
-/
theorem erdos_problem_1110 :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      ¬(p = 3 ∧ q = 2) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} :=
  sorry

/--
Variant (Erdős [Er92b]; proved by Jansen and others, solved): every
positive integer is the sum of distinct integers of the form 2^k 3^l,
none of which divide any other — that is, every positive integer is
(3,2)-representable. This is the "silly conjecture" whose simple
inductive proof is sketched in the module docstring, and it is why the
case {p,q} = {2,3} is excluded from the main problem.
-/
theorem erdos_problem_1110_jansen :
    ∀ n : ℕ, 0 < n → IsRepresentable 3 2 n :=
  sorry

/--
Variant (Erdős–Lewin theorem [ErLe96], solved): for coprime integers
p > q ≥ 2, the set of non-representable numbers is finite if and only if
{p,q} = {2,3} — i.e. p = 3 and q = 2, given the convention p > q.
-/
theorem erdos_problem_1110_erdos_lewin :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (Set.Finite {n : ℕ | ¬IsRepresentable p q n} ↔ (p = 3 ∧ q = 2)) :=
  sorry

/--
Variant (Yu–Chen [YuCh22], solved): there are infinitely many
non-representable numbers coprime to p·q whenever q > 3, or q = 3 and
p ≠ 5, or q = 2 and p ∉ {3,5,9}. This proves the main conjecture
`erdos_problem_1110` in every case except
(p,q) ∈ {(5,2), (9,2), (5,3)}.
-/
theorem erdos_problem_1110_yu_chen_infinite :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (3 < q ∨ (q = 3 ∧ p ≠ 5) ∨ (q = 2 ∧ p ≠ 3 ∧ p ≠ 5 ∧ p ≠ 9)) →
      Set.Infinite {n : ℕ | ¬IsRepresentable p q n ∧ Nat.Coprime n (p * q)} :=
  sorry

/--
Variant (Yu–Chen [YuCh22], solved): the set of representable numbers has
natural density zero whenever q > 3, or q = 3 and p > 6, or q = 2 and
p > 10.

Density zero is encoded without real analysis (this file has no
limit/filter imports): for every k > 0, eventually every finite set T of
representable numbers below N satisfies k·|T| ≤ N. Taking T to be the
full (finite) set of representable numbers below N, this says the
counting function is eventually ≤ N/k for every k, i.e. the upper
density is ≤ 1/k for every k > 0 — which is exactly natural density
zero; conversely density zero implies the bound for every subset T.
-/
theorem erdos_problem_1110_yu_chen_density :
    ∀ p q : ℕ, 2 ≤ q → q < p → Nat.Coprime p q →
      (3 < q ∨ (q = 3 ∧ 6 < p) ∨ (q = 2 ∧ 10 < p)) →
      ∀ k : ℕ, 0 < k → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ T : Finset ℕ, (∀ n ∈ T, n < N ∧ IsRepresentable p q n) →
          k * T.card ≤ N :=
  sorry

/--
Variant (Erdős–Lewin's further question [ErLe96], answered affirmatively
by Yu–Chen [YuCh22], solved): there is a function f(n) → ∞ such that
every sufficiently large integer n can be written as a sum of integers
of the form 2^k 3^l, none of which divide another, each of which is
> f(n).

Yu and Chen [YuCh22] proved that the fastest-growing such f satisfies
n/(log n)^{log_2 3} ≪ f(n) ≪ n/log n, and Yang and Zhao [YaZh25]
improved the lower bound to f(n) ≫ n/log n. Only the qualitative
existence is formalized here; the quantitative bounds would require real
logarithms, a construct not present in this file. "f(n) → ∞" is encoded
as: for every M there is a threshold beyond which f(n) ≥ M.
-/
theorem erdos_problem_1110_erdos_lewin_growth :
    ∃ f : ℕ → ℕ,
      (∀ M : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → M ≤ f n) ∧
      ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
        ∃ S : Finset ℕ, S.Nonempty ∧
          (∀ m ∈ S, IsPQPower 3 2 m) ∧
          IsDivisibilityAntichain S ∧
          (∀ m ∈ S, f n < m) ∧
          S.sum id = n :=
  sorry

end Erdos1110

end
