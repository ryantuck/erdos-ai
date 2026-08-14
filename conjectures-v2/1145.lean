import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Erdős Problem #1145

Let $A=\{1\leq a_1<a_2<\cdots\}$ and $B=\{1\leq b_1<b_2<\cdots\}$ be sets of
integers with $a_n/b_n\to 1$. If $A+B$ contains all sufficiently large
positive integers then is it true that $\limsup 1_A\ast 1_B(n)=\infty$?

Verbatim source statement (erdosproblems.com/1145): "Let $A=\{1\leq
a_1<a_2<\cdots\}$ and $B=\{1\leq b_1<b_2<\cdots\}$ be sets of integers with
$a_n/b_n\to 1$. If $A+B$ contains all sufficiently large positive integers
then is it true that $\limsup 1_A\ast 1_B(n)=\infty$?"

Status: OPEN per erdosproblems.com/1145 (page last edited 08 February 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

Remarks from the source page:
* "A conjecture of Erdős and Sárközy. Some condition relating $A$ and $B$ is
  necessary since, for example, if $A$ is the set of all integers with only
  even binary digits and $B$ is the set of all integers with only odd binary
  digits than [sic] $1_A\ast 1_B(n)=1$ for all $n$." (Formalized below as
  `erdos_problem_1145.variants.condition_necessary`.)
* "This is a stronger form of [28]. See also [331]." (Cross-references:
  Erdős problems #28 and #331; the $A = B$ specialization — problem #28 — is
  recorded below as `erdos_problem_1145.variants.special_case_eq_erdos_28`.)

Membership of 0: the source displays $A, B \subseteq \{1, 2, \ldots\}$, but
the formalization quantifies over all `A B : Set ℕ`, so `0` may belong to
either set. This follows the site-endorsed upstream formalization
(google-deepmind/formal-conjectures `ErdosProblems/1145.lean`, linked from the
page as "Formalised statement? Yes"), whose formalization note records that
0-membership "has been left purposely ambiguous" in the site's discussion and
deliberately formalizes the 0-inclusive version. The two readings are in fact
equivalent: positive instances are 0-inclusive instances, and conversely the
shift $A' = A+1$, $B' = B+1$ turns any 0-inclusive instance into a positive
one — it preserves infinitude, $a_n/b_n \to 1$ (both sequences tend to
infinity), cofiniteness of the sumset ($A'+B' = (A+B)+2$), and boundedness of
the representation function ($r_{A',B'}(n) = r_{A,B}(n-2)$ for $n \ge 2$, else
$0$). (Informal argument; not machine-checked.) The page's own
necessity example also requires $0 \in A \cap B$ for "$1_A\ast 1_B(n)=1$ for
all $n$" to hold, supporting the 0-inclusive reading.

Additional thanks to (per the page): Felix Pernegger.
Tags: additive combinatorics, additive basis.
Formalised statement (per the page, as of access): Yes —
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1145.lean.

Reference: [Va99, 1.17]
https://www.erdosproblems.com/1145

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.17. (Honest stub; neither `/latex/1145` nor `/bibs/Va99` was captured in
  the session logs, so this identification follows the site's uniform
  bibliography for the key — corroborated by sibling problems 1068 and
  1137–1144 and by upstream formal-conjectures files captured in the logs.
  Note: glosses of `[Va99]` as "Vaughan, R. C., *The Hardy-Littlewood
  Method*, 2nd ed., 1997" appearing in the archived styled files of sibling
  problems (e.g. `deepmind/deepmind/1140.lean`, `1147.lean`) are
  hallucinations for this key.)
-/

open Set Pointwise Filter Topology

noncomputable section

/--
The representation function for sets A, B ⊆ ℕ, counting the number of ways
to write n as a + b with a ∈ A and b ∈ B.

This is the additive convolution 1_A ∗ 1_B(n) = ∑_{a+b=n} 1_A(a)·1_B(b),
counting *ordered* pairs. The defining set is always finite (it injects into
{0, …, n} via the first coordinate), so `ncard` is the true count — no
junk-value concern arises.
-/
def repFunction₂ (A B : Set ℕ) (n : ℕ) : ℕ :=
  ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}

/--
Erdős Problem #1145 [Va99, 1.17] (Open):

A conjecture of Erdős and Sárközy. Let A = {a₀ < a₁ < ⋯} and
B = {b₀ < b₁ < ⋯} be infinite sets of natural numbers with
aₙ / bₙ → 1 as n → ∞.

If A + B contains all sufficiently large positive integers, then is it true
that limsup 1_A ∗ 1_B(n) = ∞, i.e., that the representation function is
unbounded?

This is a stronger form of Erdős Problem #28 (the case A = B; see
`erdos_problem_1145.variants.special_case_eq_erdos_28`). See also #331.
Some condition relating A and B is necessary: without the hypothesis
aₙ/bₙ → 1 the representation function can be identically 1 (see
`erdos_problem_1145.variants.condition_necessary`).

Encoding notes:
* The source writes A, B ⊆ {1, 2, …}; here 0 is allowed in A and B,
  following the site-endorsed upstream formalization — the two readings are
  equivalent via the shift (A+1, B+1); see the module docstring.
* The conclusion `∀ M, ∃ n, repFunction₂ A B n ≥ M` (unboundedness) is
  equivalent to limsup_{n→∞} 1_A ∗ 1_B(n) = ∞ for ℕ-valued sequences: if
  some level set {n | r n ≥ M₀} were finite and nonempty with maximum value
  V, the level set at V+1 would be empty, contradicting unboundedness — so
  unboundedness already forces every level set to be infinite.
* `hAsymp` uses the 0-indexed enumeration `Nat.nth`; the index shift against
  the source's 1-indexing is invisible to `Tendsto _ atTop`. If 0 ∈ B the
  n = 0 term divides by zero and is 0 by Lean's convention — a single term,
  likewise invisible at `atTop` (`Nat.nth` is strictly monotone on infinite
  sets, so bₙ > 0 for n ≥ 1).
* `hBasis` (the complement of A + B in ℕ is finite) is exactly "A + B
  contains all sufficiently large positive integers".

The source poses this as a yes/no question and the problem is OPEN; this raw
corpus has no `answer()` elaborator (Mathlib-only imports), and its uniform
convention for open yes/no questions is a direct assertion of the asked
("yes") direction with a `sorry` proof, as here. In styled question form it
would be `answer(sorry) ↔ ∀ A B, …`.
-/
theorem erdos_problem_1145 (A B : Set ℕ)
    (hA : A.Infinite)
    (hB : B.Infinite)
    (hAsymp : Tendsto (fun n => (↑(Nat.nth (· ∈ A) n) : ℝ) / (↑(Nat.nth (· ∈ B) n) : ℝ)) atTop (nhds 1))
    (hBasis : {n : ℕ | n ∉ (A + B)}.Finite) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction₂ A B n ≥ M :=
  sorry

/--
Variant (solved, page-confirmed): some condition relating A and B is
necessary in Erdős Problem #1145 — there exist infinite A, B ⊆ ℕ with
1_A ∗ 1_B(n) = 1 for *every* n (so A + B = ℕ, every hypothesis of the main
statement except aₙ/bₙ → 1 holds, yet the representation function is as
bounded as it can be).

Witness (from the source page): A = the set of integers whose binary
expansion has 1s only in even positions (equivalently, sums ∑ εᵢ·4^i),
B = the set of integers whose binary expansion has 1s only in odd positions
(sums ∑ εᵢ·2·4^i). Splitting the binary digits of n into even and odd
positions gives the unique decomposition n = a + b with a ∈ A, b ∈ B (no
carries occur since the bit supports are disjoint), so 1_A ∗ 1_B ≡ 1. Note
0 ∈ A ∩ B is required (e.g. n = 1 = 1 + 0), consistent with the 0-inclusive
reading; and aₙ/bₙ → 1 fails here (in fact bₙ = 2aₙ), consistent with the
main conjecture being open. Not compile-verified.
-/
theorem erdos_problem_1145.variants.condition_necessary :
    ∃ A B : Set ℕ, A.Infinite ∧ B.Infinite ∧ ∀ n : ℕ, repFunction₂ A B n = 1 :=
  sorry

/--
Variant (open, page-confirmed cross-reference): the A = B specialization of
Erdős Problem #1145 is exactly Erdős Problem #28 (Erdős–Turán-type
conjecture): if A ⊆ ℕ is infinite and A + A contains all sufficiently large
integers, is the representation function of A + A unbounded?

The page states #1145 "is a stronger form of [28]": taking B = A makes the
ratio sequence aₙ/aₙ eventually constantly 1 (the n = 0 term may be 0/0 = 0
if 0 ∈ A, which `Tendsto _ atTop` ignores), so this statement follows from
`erdos_problem_1145`. It is itself open. Not compile-verified.
-/
theorem erdos_problem_1145.variants.special_case_eq_erdos_28 (A : Set ℕ)
    (hA : A.Infinite)
    (hBasis : {n : ℕ | n ∉ (A + A)}.Finite) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction₂ A A n ≥ M :=
  sorry

end
