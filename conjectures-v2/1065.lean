import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #1065

Are there infinitely many primes p such that p = 2^k · q + 1 for some prime q
and k ≥ 0? Or p = 2^k · 3^l · q + 1?

Status: OPEN (erdosproblems.com/1065, page last edited 30 September 2025;
the site notes it "cannot be resolved with a finite computation").

This is mentioned in problem B46 of Guy's collection [Gu04].

An upstream formalization exists at google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1065.lean` (namespace `Erdos1065`); that
file is the authoritative artifact and is not present in this repository.

Reference: https://www.erdosproblems.com/1065
Tags: number theory
Related OEIS sequences: A074781, A339465

[Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004),
xviii+437. Problem B46.
-/

/--
Erdős Problem #1065 [Gu04]:

Are there infinitely many primes p such that p = 2^k * q + 1 for some prime q
and k ≥ 0?
-/
theorem erdos_problem_1065a :
    {p : ℕ | p.Prime ∧ ∃ k : ℕ, ∃ q : ℕ, q.Prime ∧ p = 2 ^ k * q + 1}.Infinite :=
  sorry

/--
Erdős Problem #1065 (second part) [Gu04]:

Are there infinitely many primes p such that p = 2^k * 3^l * q + 1 for some
prime q and k, l ≥ 0?
-/
theorem erdos_problem_1065b :
    {p : ℕ | p.Prime ∧ ∃ k l : ℕ, ∃ q : ℕ, q.Prime ∧ p = 2 ^ k * 3 ^ l * q + 1}.Infinite :=
  sorry
