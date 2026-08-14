import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Classical

/-!
# Erdős Problem #1103

Verbatim statement (erdosproblems.com/1103):

Let $A$ be an infinite sequence of integers such that every $n \in A + A$ is
squarefree. How fast must $A$ grow?

Status on erdosproblems.com/1103: OPEN — "This is open, and cannot be resolved
with a finite computation." (Page edition 03 December 2025, accessed
2026-02-23.) Source citation on the page: [Er81h, p.180]. Tags: number theory.

(The page says "integers"; its remarks write $A = \{a_1 < a_2 < \cdots\}$ with
$a_j > 0.24\,j^{4/3}$, so the standard reading — taken by this file — is a
strictly increasing sequence of positive integers. Over ℕ the positivity is
forced anyway: $2a_0 \in A + A$ must be squarefree and `Squarefree 0` is false
in Mathlib, so $a_0 \ge 1$.)

Remarks from the page: Erdős notes there exists such a sequence which grows
exponentially, but does not expect such a sequence of polynomial growth. In
[Er81h] he asked whether there is an infinite sequence of integers $A$ such
that, for every $a \in A$ and prime $p$, if $a \equiv t \pmod{p^2}$ then
$1 \le t < p^2/2$; he noted such a sequence has every $n \in A + A$ squarefree,
and wrote "I am doubtful if such a sequence exists." Indeed, there are
trivially at most finitely many such $a$, since there cannot be any primes
$p \in (a^{1/2}, (2a)^{1/2}]$, but there exist primes in $(x, \sqrt{2}x)$ for
all large $x$. (That finiteness remark is not formalized here: `Nat.Prime` is
not among this file's constructs, per the pipeline's constructs-already-present
rule; recorded in prose only.)

If $A = \{a_1 < a_2 < \cdots\}$ is such a sequence then van Doorn and Tao
[vDTa25] have shown that $a_j > 0.24\,j^{4/3}$ for all $j$, and further that
there exists such a sequence (furthermore with squarefree terms) such that
$a_j < \exp(5j/\log j)$ for all large $j$. A superior lower bound of
$a_j \gg j^{15/11 - o(1)}$ had earlier been found by Konyagin [Ko04] when
considering the finite case — Erdős Problem #1109, the finite analogue of this
problem (formalized in `conjectures/1109.lean`; Konyagin's bound belongs to
that problem and is cited here for context only). Van Doorn and Tao also
obtain further results for the generalisation from squarefree to $k$-free
integers, and for $A \cup (A+A) \cup (A+A+A)$ in place of $A + A$ (the page
states no precise bounds for these; not formalized).

Related OEIS sequence: A392164.

References (honest stubs, recovered from the original pipeline's fetch of
erdosproblems.com/latex/1103, preserved in the session logs only as a fetch
agent's structured extraction, not raw HTML):

- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative
  number theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981),
  171–182. This problem: p. 180. (Corroborated verbatim by the independent
  `/latex/1100` extraction and by sibling files `deepmind/deepmind/18.lean`
  and `deepmind/deepmind/840.lean`. Volume number unknown — DEFERRED.)
- [Ko04] Konyagin, S. V., _Problems of the set of square-free numbers_. Izv.
  Ross. Akad. Nauk Ser. Mat. (2004), 63–90. (Matches sibling
  `deepmind/deepmind/1109.lean`. Volume number unknown — DEFERRED.)
- [vDTa25] van Doorn, W. and Tao, T., _Growth rates of sequences governed by
  the squarefree properties of its translates_. arXiv:2512.01087 (2025).
  (Title and arXiv id rest on the single `/latex/1103` extraction —
  uncorroborated, treat with that caveat. The title _Sumsets of squarefree
  numbers_ recorded for this key in `deepmind/deepmind/1103.lean` is
  model-written, contradicts this extraction, and sits in the same block as a
  demonstrably wrong [Er81h] title — not carried here.)

NOTE: the docstring enrichments and the variants below are from the fable
review of 2026-08-13 and are not compile-verified (the review container
cannot run `lake build`).

Tags: number theory
-/

/--
Erdős Problem #1103 (OPEN) [Er81h, p.180]:

For any strictly increasing sequence a : ℕ → ℕ such that a(i) + a(j) is
squarefree for all i, j, the sequence must grow super-polynomially: for every
C > 0, we have a(j) > j^C for all sufficiently large j.

This is the standard "super-polynomial growth" reading of the page's
open-ended question "How fast must A grow?", in the direction of Erdős's
recorded expectation. Note it is formally *stronger* than the literal negation
of "such a sequence of polynomial growth [exists]": the literal negation only
requires each valid sequence to escape every fixed polynomial bound, not to
exceed every polynomial eventually — see
`erdos_problem_1103.variants.no_polynomial_growth` for that literal form,
which this eventual form implies. (For C ≤ 1 the conclusion already follows
from strict monotonicity and the forced a(0) ≥ 1, since a(j) ≥ a(0) + j > j;
the content is at C > 1.)
-/
theorem erdos_problem_1103
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (j : ℝ) ^ C < (a j : ℝ) :=
  sorry

/--
Erdős Problem #1103, literal form of Erdős's expectation (OPEN) [Er81h, p.180]:

There is no strictly increasing sequence with all pairwise sums squarefree
that has polynomial growth, i.e. that is eventually bounded by K·j^C for some
constants K, C > 0. This is the literal negation of "such a sequence of
polynomial growth [exists]" from the page's remarks. It is implied by (and is
formally weaker than) the eventual form `erdos_problem_1103`: apply that
statement with exponent C + 1 and let j → ∞. The polynomial bound is stated
eventually (∃ N) rather than for all j, both because "growth" is an asymptotic
notion and because a universal bound would be unsatisfiable at j = 0, where
(0 : ℝ) ^ C = 0 forces a(0) ≤ 0 against the forced a(0) ≥ 1 — an eventual
bound avoids that degeneracy trap.

NOTE: added by the fable review of 2026-08-13 from the recovered source page;
not compile-verified.
-/
theorem erdos_problem_1103.variants.no_polynomial_growth :
    ¬ ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i j : ℕ, Squarefree (a i + a j)) ∧
      ∃ C K : ℝ, C > 0 ∧ K > 0 ∧
        ∃ N : ℕ, ∀ j : ℕ, j ≥ N → (a j : ℝ) ≤ K * (j : ℝ) ^ C :=
  sorry

/--
van Doorn–Tao lower bound (SOLVED) [vDTa25]:

If A = {a₁ < a₂ < ⋯} has every element of A + A squarefree, then
a_j > 0.24·j^{4/3} for all j ≥ 1. In this file's 0-indexed convention
a(i) = a_{i+1}, whence the (j + 1) on the left-hand side — the exact
index-shifted translation of the page's 1-indexed "for all j". (Small-index
sanity check, cf. the false-page-bound trap: for j + 1 ≤ 72 the bound already
follows from strict monotonicity and a(0) ≥ 1, since then
0.24·(j+1)^{4/3} < j + 1 ≤ a(j); so the "for all j" claim has no
small-parameter counterexample.)

NOTE: added by the fable review of 2026-08-13 from the recovered source page;
not compile-verified.
-/
theorem erdos_problem_1103.variants.van_doorn_tao_lower_bound
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ j : ℕ, (0.24 : ℝ) * ((j : ℝ) + 1) ^ ((4 : ℝ) / 3) < (a j : ℝ) :=
  sorry

/--
van Doorn–Tao construction (SOLVED) [vDTa25]:

There exists a strictly increasing sequence — with squarefree terms, moreover —
such that every element of A + A is squarefree and a_j < exp(5j/log j) for all
large j. In this file's 0-indexed convention a(i) = a_{i+1}, so the bound is
stated at j + 1: the exact index-shifted translation of the page's 1-indexed
claim (with an eventual bound the shift is otherwise harmless, but the
translated form is the one the source licenses). The eventual quantifier also
keeps the j = 0 and j = 1 degeneracies of `Real.log` (log 1 = 0, division by
zero returning 0, exp 0 = 1) below the threshold N.

`Real.exp` and `Real.log` are relied on as transitive imports of
`Mathlib.Analysis.SpecialFunctions.Pow.Real` (real rpow is defined via exp and
log); this is the one construct not already literally present in the file —
flagged for the compile pass.

NOTE: added by the fable review of 2026-08-13 from the recovered source page;
not compile-verified.
-/
theorem erdos_problem_1103.variants.van_doorn_tao_upper_construction :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i j : ℕ, Squarefree (a i + a j)) ∧
      (∀ i : ℕ, Squarefree (a i)) ∧
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (a j : ℝ) < Real.exp (5 * ((j : ℝ) + 1) / Real.log ((j : ℝ) + 1)) :=
  sorry

end
