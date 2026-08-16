import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Pointwise Filter

/-!
# Erdős Problem #28

If $A \subseteq \mathbb{N}$ is such that $A + A$ contains all but finitely
many integers then $\limsup 1_A \ast 1_A(n) = \infty$.

This is the Erdős–Turán conjecture on additive bases, conjectured by Erdős
and Turán [ErTu41].

**Status: OPEN** — banner tooltip: "This is open, and cannot be resolved
with a finite computation." **$500** prize. (erdosproblems.com/28, page
last edited 23 January 2026, accessed 2026-03-05; the teorth/erdosproblems
metadata mirror agrees: state "open", last update 2025-08-31, prize $500.)

Remarks from the source page:

- Erdős and Turán also suggest the stronger conjecture that
  $\limsup 1_A \ast 1_A(n)/\log n > 0$.
  (Formalized below as `erdos_problem_28.variants.log_growth`.)
- Another stronger conjecture would be that the hypothesis
  $\lvert A \cap [1, N] \rvert \gg N^{1/2}$ for all large $N$ suffices.
  (Formalized below as `erdos_problem_28.variants.counting_hypothesis`.)
- See also [40], and [1145] for a stronger generalisation. (Both are
  formalized in this corpus — `conjectures/40.lean`,
  `conjectures/1145.lean` — with the same `∀ M, ∃ n` unboundedness
  encoding and matching representation-function conventions.)
- This is discussed in problem C9 of Guy's collection [Gu04].

## References

Problem sources on the page: [ErTu41] [Er56] [Er57] [Er59] [Er61] [Er65]
[Er65b] [Er69] [Er70c] [Er73] [Er77c] [ErGr80] [Er81] [Er85c] [Er89d]
[Er90] [Er94b] [Er95] [Er97c] [Er97f] [Va99, 1.16]; remarks cite [Gu04].

- [ErTu41] Erdős, P. and Turán, P., _On a problem of Sidon in additive
  number theory, and on some related problems_. J. London Math. Soc. 16
  (1941), 212-215. (Stub: the page capture carries only the key; the
  bibliographic details are reviewer knowledge, unverified offline — no
  `/latex/28` fetch exists in the session logs.)
- [Gu04] Guy, R. K., _Unsolved problems in number theory_. 3rd ed.,
  Springer, 2004. (Stub: details from sibling corpus files
  `deepmind/deepmind/1053.lean`, `deepmind/deepmind/1057.lean`;
  unverified offline.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his Mathematics" (Budapest, 1999). (Stub:
  details from sibling corpus files, e.g. `deepmind/deepmind/1032.lean`;
  `conjectures/1145.lean` cites the same collection as [Va99, 1.17].
  Unverified offline.)
- The remaining seventeen `Er*` keys are Erdős's problem papers, given on
  the page as bare citation keys; no bibliographic data for them is
  recoverable from the session logs (no `/latex/28` fetch was ever made):
  DEFERRED.

No related OEIS sequences (mirror: "N/A"). 4 forum comments.
Formalised statement? **Yes** — upstream google-deepmind/formal-conjectures
`FormalConjectures/ErdosProblems/28.lean` (present at HEAD dd1c2beb) states
the same hypothesis `(A + A)ᶜ.Finite` and the conclusion
`limsup (fun n => (sumRep A n : ℕ∞)) atTop = ⊤`, where its `sumRep` counts
exactly the ordered pairs counted by `repFunction` below.

Tags: number theory, additive basis
https://www.erdosproblems.com/28
-/

/--
The representation function for a set A ⊆ ℕ, counting the number of ways
to write n as a + b with a, b ∈ A — ordered pairs, so a + b and b + a
count separately when a ≠ b. This is the convolution square
$1_A \ast 1_A(n) = \sum_{a+b=n} 1_A(a) 1_A(b)$.

The defining set injects into {0, …, n} via the first coordinate (the
second is determined as n - p.1), hence is finite, so `Set.ncard` (which
takes the junk value 0 on infinite sets) computes the true count here for
every input.
-/
noncomputable def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/--
Erdős Problem #28 [ErTu41, Er56, Er57, Er59, Er61, Er65, Er65b, Er69,
Er70c, Er73, Er77c, ErGr80, Er81, Er85c, Er89d, Er90, Er94b, Er95,
Er97c, Er97f, Va99 1.16]:

If $A \subseteq \mathbb{N}$ is such that $A + A$ contains all but finitely
many integers then $\limsup 1_A \ast 1_A(n) = \infty$.

The Erdős–Turán conjecture on additive bases [ErTu41]; OPEN, $500 prize.

The conclusion $\limsup_n 1_A \ast 1_A(n) = \infty$ is encoded as
unboundedness: for every M there exists n with `repFunction A n ≥ M`.
For an ℕ-valued sequence the two are equivalent: if the sequence is
unbounded but some threshold M were exceeded at only finitely many
indices, the sequence's values on that finite index set would be bounded,
contradicting that arbitrarily large values occur — so every threshold is
exceeded infinitely often, which is $\limsup = \infty$.
-/
theorem erdos_problem_28 (A : Set ℕ)
    (h : {n : ℕ | n ∉ (A + A)}.Finite) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction A n ≥ M :=
  sorry

/--
Stronger conjecture of Erdős and Turán, from the remarks on the source
page [ErTu41]: under the same hypothesis,
$\limsup 1_A \ast 1_A(n)/\log n > 0$.

A positive limsup of $r(n)/\log n$ is encoded as: some real $c > 0$ has
$r(n) \geq c \log n$ for infinitely many n (`∃ᶠ n in atTop`). This is
equivalent to $\limsup > 0$ (take c below the limsup if it is finite, any
c if it is infinite) and avoids Mathlib's junk-valued `limsup` on
unbounded real-valued sequences. The finitely many indices n ≤ 1, where
`Real.log n = 0` makes the inequality trivial, are invisible to the
frequency filter.
-/
theorem erdos_problem_28.variants.log_growth (A : Set ℕ)
    (h : {n : ℕ | n ∉ (A + A)}.Finite) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, c * Real.log n ≤ (repFunction A n : ℝ) :=
  sorry

/--
Stronger conjecture from the remarks on the source page: the hypothesis
$\lvert A \cap [1, N] \rvert \gg N^{1/2}$ for all large $N$ suffices for
the representation function to be unbounded.

This hypothesis is indeed implied by the main theorem's (so this variant
is stronger): if $A + A$ contains every $n \geq n_0$, then each such
$n \leq N$ is a sum of two elements of $A \cap [0, N]$, so
$N - n_0 \leq \lvert A \cap [0, N] \rvert^2$, giving
$\lvert A \cap [1, N] \rvert \geq \sqrt{N - n_0} - 1 \gg N^{1/2}$.
The endpoint choice $[1, N]$ versus $[0, N]$ shifts the count by at most
1 and is absorbed into the constant c.
-/
theorem erdos_problem_28.variants.counting_hypothesis (A : Set ℕ)
    (h : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ ((A ∩ Icc 1 N).ncard : ℝ)) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction A n ≥ M :=
  sorry
