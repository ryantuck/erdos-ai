import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1074

Source statement (erdosproblems.com/1074, verbatim): "Let $S$ be the set of
all $m\geq 1$ such that there exists a prime $p\not\equiv 1\pmod{m}$ such
that $m!+1\equiv 0\pmod{p}$. Does $\lim |S\cap [1,x]|/x$ exist? What is it?

Similarly, if $P$ is the set of all primes $p$ such that there exists an $m$
with $p\not\equiv 1\pmod{m}$ such that $m!+1\equiv 0\pmod{p}$, then does
$\lim |P\cap [1,x]|/\pi(x)$ exist? What is it?"

Status: **OPEN** (page edition 04 October 2025).

Questions raised by Erdős, Hardy, and Subbarao [HaSu02], who called the set S
"EHS numbers" and the set P "Pillai primes", and proved that both S and P are
infinite. (The intended range of m is m ≥ 1 in both definitions.) Pillai
[Pi30] raised the question of whether there exist any primes in P; this was
answered by Chowla, who noted that, for example,
14! + 1 ≡ 18! + 1 ≡ 0 (mod 23). The sequence S begins
8, 9, 13, 14, 15, 16, 17, … (OEIS A064164). The sequence P begins
23, 29, 59, 61, 67, 71, … (OEIS A063980).

Regarding the first question, Hardy and Subbarao computed all EHS numbers up
to 2^10, and write "...if this trend conditions [sic] we expect [the limit]
to be around 0.5, if it exists. The frequency with which the EHS numbers
occur - most often in long sequences of consecutive integers - makes us
believe that their asymptotic density exists and is unity. Erdős, though
initially hesitant, later agreed with this view."

Regarding the second question, they write "[from the data] it would appear
that if the limit exists, it is perhaps between 0.5 and 0.6. But then there
seems to be no reason why the ratio should not tend to 1, even though very
slowly and certainly not monotonically."

This is discussed in problem A2 of Guy's collection [Gu04].

The two main theorems below formalize the *conjectured* answers (each limit
exists and equals 1 — the belief recorded in [HaSu02], firm for S and
tentative for P); the `..._exists` companion statements formalize the literal
"does the limit exist?" questions, and the remaining statements record the
solved facts from the page's remarks.

References:

[HaSu02] Hardy, G. E. and Subbarao, M. V., *A modified problem of Pillai and
some related questions*. Amer. Math. Monthly (2002), 554–559.

[Pi30] Pillai (1930). (Bibliographic details beyond the citation key were not
recoverable from the archived page; attribution per the page's remarks.)

[Gu04] Guy, R. K., *Unsolved problems in number theory*. 3rd ed., Springer
(2004).

https://www.erdosproblems.com/1074
(Archived captures accessed 2026-02-22 and 2026-03-09, in agreement. The
problem is also formalized upstream in google-deepmind/formal-conjectures,
FormalConjectures/ErdosProblems/1074.lean, which is the authoritative
artifact for that repository.)
-/

/-- An "EHS number": m ≥ 1 such that some prime p ≢ 1 (mod m) divides m! + 1. -/
def IsEHSNumber (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ p : ℕ, Nat.Prime p ∧ p ∣ (m.factorial + 1) ∧ ¬(p % m = 1 % m)

/-- A "Pillai prime": a prime p such that some m ≥ 1 has p ∣ m! + 1 and p ≢ 1 (mod m).

The guard `1 ≤ m` is essential: without it, `m = 0` gives `0! + 1 = 2` and
`¬(p % 0 = 1 % 0)` reduces to `p ≠ 1`, so `2` would spuriously count as a
Pillai prime — contradicting the sequence P = 23, 29, 59, … (OEIS A063980). -/
def IsPillaiPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m : ℕ, 1 ≤ m ∧ p ∣ (m.factorial + 1) ∧ ¬(p % m = 1 % m)

/-- Count of EHS numbers in [1, N]. -/
noncomputable def ehsCount (N : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun m => IsEHSNumber m)).card

/-- Count of Pillai primes in [1, N]. -/
noncomputable def pillaiPrimeCount (N : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => IsPillaiPrime p)).card

/-- Count of all primes in [1, N]. -/
noncomputable def primeCount1074 (N : ℕ) : ℕ :=
  ((range (N + 1)).filter (fun p => Nat.Prime p)).card

/--
Erdős Problem #1074, Part (a) [HaSu02]:

Source question: does lim |S ∩ [1,x]| / x exist? What is it? (OPEN.)

This statement formalizes the conjectured answer: the asymptotic density of
EHS numbers exists and equals 1 — per [HaSu02], whose authors "believe that
their asymptotic density exists and is unity. Erdős, though initially
hesitant, later agreed with this view."
-/
theorem erdos_problem_1074a :
    Tendsto
      (fun N : ℕ => (ehsCount N : ℝ) / (N : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1074, Part (b) [HaSu02]:

Source question: does lim |P ∩ [1,x]| / π(x) exist? What is it? (OPEN.)

This statement formalizes the (tentatively) conjectured answer: the relative
density of Pillai primes among all primes exists and equals 1. Note that
[HaSu02] is hedged here: from the data "it would appear that if the limit
exists, it is perhaps between 0.5 and 0.6. But then there seems to be no
reason why the ratio should not tend to 1, even though very slowly and
certainly not monotonically."
-/
theorem erdos_problem_1074b :
    Tendsto
      (fun N : ℕ => (pillaiPrimeCount N : ℝ) / (primeCount1074 N : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1074, Part (a), literal existence question:
does lim |S ∩ [1,x]| / x exist? (OPEN; implied by `erdos_problem_1074a`.)
-/
theorem erdos_problem_1074a_exists :
    ∃ c : ℝ, Tendsto
      (fun N : ℕ => (ehsCount N : ℝ) / (N : ℝ))
      atTop (nhds c) :=
  sorry

/--
Erdős Problem #1074, Part (b), literal existence question:
does lim |P ∩ [1,x]| / π(x) exist? (OPEN; implied by `erdos_problem_1074b`.)
-/
theorem erdos_problem_1074b_exists :
    ∃ c : ℝ, Tendsto
      (fun N : ℕ => (pillaiPrimeCount N : ℝ) / (primeCount1074 N : ℝ))
      atTop (nhds c) :=
  sorry

/--
Erdős, Hardy, and Subbarao [HaSu02] proved that the set S of EHS numbers is
infinite.
-/
theorem erdos_problem_1074_S_infinite :
    ∀ N : ℕ, ∃ m : ℕ, N < m ∧ IsEHSNumber m :=
  sorry

/--
Erdős, Hardy, and Subbarao [HaSu02] proved that the set P of Pillai primes is
infinite.
-/
theorem erdos_problem_1074_P_infinite :
    ∀ N : ℕ, ∃ p : ℕ, N < p ∧ IsPillaiPrime p :=
  sorry

/--
Pillai [Pi30] asked whether any Pillai primes exist. Chowla answered
affirmatively: 14! + 1 ≡ 18! + 1 ≡ 0 (mod 23) and 23 ≢ 1 (mod 14), so 23 is
a Pillai prime (the smallest, per OEIS A063980).
-/
theorem erdos_problem_1074_pillai_23 : IsPillaiPrime 23 :=
  sorry

end
