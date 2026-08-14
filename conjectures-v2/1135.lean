import Mathlib.Data.Nat.Basic

/-!
# Erdős Problem #1135

Define f : ℕ → ℕ by f(n) = n/2 if n is even and f(n) = (3n+1)/2 if n is odd.

Given any integer m ≥ 1, does there exist k ≥ 1 such that f^(k)(m) = 1?

Status on erdosproblems.com/1135: OPEN ("This is open, and cannot be resolved
with a finite computation."); prize banner "$500". Page last edited
12 January 2026, accessed 2026-03-09. Tags: number theory, iterated functions.
Related OEIS sequences: A006370, A008908.

This is the infamous Collatz conjecture (in its "shortcut" form, where the odd
step is (3n+1)/2 rather than 3n+1). For a detailed discussion of the history
and theory surrounding this problem see the overview by Lagarias [La10].

Page remarks: this is not a problem due to Erdős; it was first devised by
Collatz before 1952. Erdős referred to this problem on several occasions as
'hopeless'. As Lagarias [La16] notes, the closest Erdős ever came to working
on problems of this nature is the theorem described in the remarks to
Erdős Problem #1134 (the Klarner–Rado counting theorem — see
`conjectures-v2/1134.lean`).

It is often claimed that Erdős offered $500 for a solution; this claim
originated in a survey article by Lagarias [La85]. Lagarias reported, in
personal communication, that this came from a conversation he had with Erdős
and Graham around 1983, in which Graham asked Erdős to estimate what value
Erdős would put the problem on his prize scale, to which Erdős replied $500.
Strictly speaking, Erdős never offered $500 specifically as a prize; the page
records the value for comparison with Erdős's other 'prize problems'.

This is Problem E16 in Guy's collection [Gu04], in which Guy quotes Erdős as
saying "Mathematics may not be ready for such problems".

References (page citation keys [La85], [Er97e, p.537], [La16]; remarks cite
[La10] and [Gu04]. Bibliographic data below is recovered from the upstream
formal-conjectures ErdosProblems/1135.lean captured in the session logs;
volume numbers were absent from the recovered data and are deliberately not
invented):

- [La85] Lagarias, J. C., _The 3x+1 problem and its generalizations_.
  American Mathematical Monthly (1985), 3–23.
- [Er97e] Erdős, P. (1997). (Stub: the /latex/1135 bibliography was not
  captured in the logs; sibling files in this corpus carry two conflicting
  titles for this key and the upstream formal-conjectures file omits it, so
  only the author and year are recorded here. DEFERRED.)
- [La16] Lagarias, J. C., _Erdős, Klarner, and the 3x+1 problem_.
  American Mathematical Monthly (2016), 753–776.
- [La10] Lagarias, J. C., _The 3x+1 problem: an overview_. (2010), 3–29.
- [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.

NOTE: the definitions and the theorem statement below are unchanged from the
input file (`conjectures/1135.lean`) — the Fable review of 2026-08-14 found
no semantic defects in them. Only the documentation (bibliography, status,
page remarks, and a corrected quote attribution) was added by that review;
the file is NOT compile-verified in this container (the input compiled
successfully in the original pipeline session).
-/

/--
The Collatz function (shortcut form): f(n) = n/2 if n is even,
f(n) = (3n+1)/2 if n is odd. Both ℕ-divisions are exact: n/2 when n is even,
and (3n+1)/2 when n is odd (since 3n+1 is then even).
-/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/--
The k-th iterate of the Collatz function (`collatzIter 0 n = n`).
-/
def collatzIter (k : ℕ) (n : ℕ) : ℕ :=
  match k with
  | 0 => n
  | k + 1 => collatzStep (collatzIter k n)

/--
Erdős Problem #1135 [La85][Er97e, p.537][La16] — OPEN ($500):

Define f : ℕ → ℕ by f(n) = n/2 if n is even and f(n) = (3n+1)/2 if n is odd.

Given any integer m ≥ 1, does there exist k ≥ 1 such that f^(k)(m) = 1?

This is the infamous Collatz conjecture; see the overview [La10]. It is not a
problem due to Erdős; it was first devised by Collatz before 1952. Erdős
referred to this problem on several occasions as 'hopeless', and Guy [Gu04]
(where this is Problem E16) quotes Erdős as saying "Mathematics may not be
ready for such problems".

Stated as a direct assertion of the asked ("yes") direction per this corpus's
raw-file convention for open questions; a styled version would use the
`answer(sorry) ↔` question form.
-/
theorem erdos_problem_1135 :
    ∀ m : ℕ, 1 ≤ m → ∃ k : ℕ, 1 ≤ k ∧ collatzIter k m = 1 :=
  sorry
