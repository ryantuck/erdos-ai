import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic

open Classical Nat Filter Finset

noncomputable section

/-!
# Erdős Problem #1064

Prove that φ(n) > φ(n - φ(n)) for almost all n, but that φ(n) < φ(n - φ(n))
for infinitely many n, where φ is Euler's totient function.

Reference: [Er80f]
https://www.erdosproblems.com/1064

Status: PROVED — solved in the affirmative.

Solved by Luca and Pomerance [LuPo02], who proved that the set A_> of n where
φ(n) > φ(n - φ(n)) has density 1. Grytczuk, Luca, and Wójtowicz [GLW01]
had earlier shown that A_> has lower density at least 0.54 and that the set
A_< of n where φ(n) < φ(n - φ(n)) is infinite. Indeed, for any k ≥ 1, if
n = 15 · 2^k then φ(n) = 4 · 2^k while n - φ(n) = 11 · 2^k gives
φ(n - φ(n)) = 5 · 2^k, so n ∈ A_<. The sequence A_< begins
30, 60, 66, 120, … (OEIS A051488).

Luca and Pomerance [LuPo02] in fact proved more: for any function f(n) = o(n),
φ(n) > φ(n - φ(n)) + f(n) for almost all n; and for any constant c > 0, the
inequality φ(n) < c · φ(n - φ(n)) holds for infinitely many n.

There are also infinitely many n with φ(n) = φ(n - φ(n)) (OEIS A051487).
The problem page offers the family 3 · 2^k "for any k"; this holds for k ≥ 1
(φ(3 · 2^k) = 2^k and 3 · 2^k - 2^k = 2^(k+1) with φ(2^(k+1)) = 2^k) but
fails at k = 0, since φ(3) = 2 ≠ 1 = φ(3 - 2).

This problem is mentioned in Problem B42 of Guy's collection [Gu04].

The problem page links an upstream formalization in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1064.lean),
which is the authoritative formal artifact for this problem; this file is an
independent formalization. [Problem page last edited 06 October 2025;
accessed 2026-03-06.]

References (recovered from the archived problem page and repository sources;
entries are honest stubs where full bibliographic data was not recoverable):
- [Er80f] Erdős, P. — source of the problem (citation key from the problem
  page; bibliographic details not recovered).
- [GLW01] Grytczuk, Luca, and Wójtowicz — proved A_> has lower density at
  least 0.54 and A_< is infinite (bibliographic details not recovered).
- [LuPo02] Luca, Florian and Pomerance, Carl, "On some problems of
  Mąkowski–Schinzel and Erdős …" (title recovered, truncated, from the
  upstream formal-conjectures file; journal data not recovered).
- [Gu04] Guy, Richard K., *Unsolved problems in number theory*. (2004),
  xviii+437. Problem B42.
-/

/-- Count of integers m ∈ {1, ..., N} satisfying predicate P. -/
noncomputable def countSat1064 (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((range N).filter (fun n => P (n + 1))).card

/--
Erdős Problem #1064, Part (a):

φ(n) > φ(n - φ(n)) for almost all n. That is, the natural density of the set
{n : φ(n) > φ(n - φ(n))} is 1.

We require n > φ(n) (i.e., n ≥ 2) so that n - φ(n) is a positive natural
number; this also avoids leaning on the Mathlib junk value φ(0) = 0 at n = 1.
The guard excludes only the single point n = 1 and does not affect the
density. Proved by Luca and Pomerance [LuPo02].
-/
theorem erdos_problem_1064a :
    Tendsto
      (fun N : ℕ =>
        (countSat1064 (fun n => n ≥ 2 ∧ n.totient > (n - n.totient).totient) (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1064, Part (b):

φ(n) < φ(n - φ(n)) for infinitely many n. Proved by Grytczuk, Luca, and
Wójtowicz [GLW01]; for example n = 15 · 2^k for any k ≥ 1.
-/
theorem erdos_problem_1064b :
    Set.Infinite {n : ℕ | n ≥ 2 ∧ n.totient < (n - n.totient).totient} :=
  sorry

/--
Related (problem page remark; OEIS A051487):

There are infinitely many n with φ(n) = φ(n - φ(n)) — for example
n = 3 · 2^k for any k ≥ 1 (the page's "for any k" fails at k = 0, since
φ(3) = 2 ≠ 1 = φ(1)).
-/
theorem erdos_problem_1064_eq_infinite :
    Set.Infinite {n : ℕ | n ≥ 2 ∧ n.totient = (n - n.totient).totient} :=
  sorry

/--
Grytczuk–Luca–Wójtowicz [GLW01]:

The set {n : φ(n) > φ(n - φ(n))} has lower density at least 0.54. Encoded
without liminf: for every ε > 0 the counting ratio eventually exceeds
0.54 - ε.
-/
theorem erdos_problem_1064_lower_density :
    ∀ ε : ℝ, ε > 0 →
      ∀ᶠ N : ℕ in atTop,
        (countSat1064 (fun n => n ≥ 2 ∧ n.totient > (n - n.totient).totient) (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ) > 0.54 - ε :=
  sorry

/--
Luca–Pomerance strengthening [LuPo02]:

For any f : ℕ → ℕ with f(n) = o(n) — encoded as f(n)/n → 0, which is
equivalent for ℕ-valued f along atTop — we have φ(n) > φ(n - φ(n)) + f(n)
for almost all n.
-/
theorem erdos_problem_1064_strengthened (f : ℕ → ℕ)
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)) atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ =>
        (countSat1064 (fun n => n ≥ 2 ∧ (n - n.totient).totient + f n < n.totient)
            (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Luca–Pomerance [LuPo02]:

For any constant c > 0, the inequality φ(n) < c · φ(n - φ(n)) holds for
infinitely many n.
-/
theorem erdos_problem_1064_ratio (c : ℝ) (hc : c > 0) :
    Set.Infinite
      {n : ℕ | n ≥ 2 ∧ (n.totient : ℝ) < c * ((n - n.totient).totient : ℝ)} :=
  sorry

end
