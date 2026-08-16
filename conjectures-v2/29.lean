import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic

open Filter Asymptotics Classical

/-!
# Erdős Problem #29

Is there an explicit construction of a set $A \subseteq \mathbb{N}$ such that
$A + A = \mathbb{N}$ but $1_A \ast 1_A(n) = o(n^\epsilon)$ for every
$\epsilon > 0$?

**Status: PROVED** — banner tooltip: "This has been solved in the
affirmative." $100 prize. (erdosproblems.com/29, page last edited
28 December 2025; the teorth/erdosproblems metadata mirror agrees: state
"proved", last update 2025-08-31.)

Remarks from the source page:

- The existence of such a set was asked by Sidon to Erdős in 1932. Erdős
  (eventually) proved the existence of such a set using probabilistic
  methods. This problem asks for a constructive solution.
- An explicit construction was given by Jain, Pham, Sawhney, and Zakharov
  [JPSZ24].

The notion of an *explicit* construction has no canonical formalization; the
theorem below asserts the existence statement only — the true direction of
the solved problem. One faithful sharpening would demand a computable
characteristic function (`∃ f : ℕ → Bool, Computable f ∧ …`); it is not
added here because it needs constructs and imports not already present in
this file, plus an interpretive choice ("explicit" ↦ "computable") that the
source does not itself make.

## References

Problem sources on the page: [ErGr80, p.48], [Er89d], [Er95], [Er97c].

- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980), p. 48. (Key and page pin from the page capture; title/publisher
  from sibling corpus files sharing this site-global key, e.g.
  `conjectures/328.lean`, `deepmind/deepmind/29.lean` — unverified offline.)
- [Er89d] Erdős, P. (1989). (Stub: the log-recovered `/latex/29` extraction
  contains no entry for this key; details DEFERRED.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas 1 (1995), 165-186. (Stub: key from
  the page capture; title/journal/pages from sibling corpus files sharing
  this site-global key, e.g. `conjectures-v2/25.lean`,
  `deepmind/deepmind/29.lean` — unverified offline.)
- [Er97c] Erdős, P. (1997). (Stub: the log-recovered `/latex/29` extraction
  contains no entry for this key; sibling corpus files expand it with a
  graph-theory title that may not apply to this number-theory problem —
  details DEFERRED.)
- [JPSZ24] Jain, V., Pham, H. T., Sawhney, M., and Zakharov, D., _An
  explicit economical additive basis_. arXiv:2405.08650 (2024). (Full entry
  from the log-recovered `/latex/29` extraction.)

No related OEIS sequences (mirror: "N/A").
Formalised statement? No, per the page capture and the mirror
("unformalized"); upstream google-deepmind/formal-conjectures has no
`ErdosProblems/29.lean` at HEAD dd1c2beb.

Tags: number theory, additive basis
https://www.erdosproblems.com/29
-/

/--
The additive representation function $r_A(n) = (1_A \ast 1_A)(n)$ counts the
number of ordered pairs $(a, b)$ with $a, b \in A$ and $a + b = n$: each
`a ∈ {0, …, n}` with `a ∈ A ∧ n - a ∈ A` corresponds to exactly one such
pair `(a, n - a)`. This is the additive (Cauchy) convolution of the
indicator function $1_A$ with itself, evaluated at $n$ — not the Dirichlet
convolution, which is its multiplicative analogue.

(The truncated subtraction `n - a` is safe: `a ∈ Finset.range (n + 1)`
guarantees `a ≤ n`. Membership in the arbitrary `Set ℕ` is decided
classically via the `open Classical` instance, whence `noncomputable`.)
-/
noncomputable def addRepFun (A : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun a => a ∈ A ∧ n - a ∈ A)).card

/--
Erdős Problem #29 [ErGr80, p.48] (PROVED, $100 prize):

Is there an explicit construction of a set $A \subseteq \mathbb{N}$ such
that $A + A = \mathbb{N}$ but $1_A \ast 1_A(n) = o(n^\epsilon)$ for every
$\epsilon > 0$?

The existence of such a set was asked by Sidon to Erdős in 1932; Erdős
(eventually) proved existence using probabilistic methods. An explicit
construction was given by Jain, Pham, Sawhney, and Zakharov [JPSZ24],
answering the question in the affirmative.

This theorem asserts the existence statement — the true direction of the
solved problem; the *explicitness* of the construction is a
meta-mathematical requirement not captured by the formalization (see the
module docstring).

(`∀ n` ranges over all of `ℕ` including `0` and `1`, forcing `0, 1 ∈ A` —
the literal reading of $A + A = \mathbb{N}$. This is equivalent in truth
value to the "all sufficiently large $n$" reading: adjoining
`{0, …, N₀}` to a witness covers the small cases while changing each
$r_A(n)$ by at most an additive constant for all but finitely many $n$,
preserving $r_A(n) = o(n^\epsilon)$.)
-/
theorem erdos_problem_29 :
    ∃ A : Set ℕ,
      (∀ n : ℕ, ∃ a ∈ A, ∃ b ∈ A, a + b = n) ∧
      ∀ ε : ℝ, 0 < ε →
        (fun n : ℕ => (addRepFun A n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ ε) :=
  sorry
