import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Ring.Pointwise.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

open scoped Pointwise

noncomputable section

/-!
# Erdős Problem #52

The sum-product problem. Verbatim statement from the source page
(erdosproblems.com/52, page last edited 23 January 2026, accessed 2026-02-22):

"Let $A$ be a finite set of integers. Is it true that for every $\epsilon>0$
$$\max( \lvert A+A\rvert,\lvert AA\rvert)\gg_\epsilon \lvert A\rvert^{2-\epsilon}?$$"

That is (unpacking the Vinogradov notation $\gg_\epsilon$): for every
$\epsilon > 0$ there exists a constant $c > 0$ (depending on $\epsilon$ only)
such that for every finite set $A \subseteq \mathbb{Z}$,
$$\max(|A+A|, |A \cdot A|) \geq c \cdot |A|^{2-\epsilon}.$$

The conjecture is due to Erdős and Szemerédi [ErSz83]. The problem is a
**yes/no question**; the theorem below states the conjectured affirmative
direction as a direct assertion (this raw corpus has no `answer()` elaborator;
the upstream formal-conjectures encoding is
`erdos_52 : answer(sorry) ↔ ∀ ε, 0 < ε → ε < 1 → ∃ C, 0 < C ∧ ∀ A, …`,
which is equivalent to the statement below — see the theorem docstring).

Status and provenance:
- Page banner at capture: **OPEN**, tooltip "This is open, and cannot be
  resolved with a finite computation", **$250 prize**, plus the site's
  standard open-status disclaimer.
- The metadata mirror (github.com/teorth/erdosproblems, data/problems.yaml,
  entry `number: "52"`) agrees: state "open" (last update **2026-05-28**,
  fresher than the page capture), prize $250, OEIS [A263996],
  tags [number theory, additive combinatorics], comment "sum-product problem".
- The upstream formal-conjectures repo (FormalConjectures/ErdosProblems/52.lean,
  present at HEAD dd1c2beb, 2026-08-16) tags `erdos_52` as `research open`
  with `answer(sorry)`.

Remarks from the source page: Erdős and Szemerédi [ErSz83] proved a lower
bound of $|A|^{1+c}$ for some constant $c>0$, and an upper bound of
$$|A|^2 \exp\left(-c\frac{\log|A|}{\log\log|A|}\right)$$
for some constant $c>0$ (so the exponent $2$ itself is not attainable). The
lower bound has been improved a number of times; the current record is
$$\max(|A+A|, |AA|) \gg |A|^{\frac{1270}{951}-o(1)}$$
due to Bloom [Bl25] (note $1270/951 = 1.33543\cdots$). There is likely nothing
special about the integers: Erdős and Szemerédi also ask the analogous
question for finite sets of real or complex numbers. For reals the best bound
is the same bound of Bloom; for complex numbers the best bound is
$\max(|A+A|,|AA|) \gg |A|^{4/3+c}$ for some absolute $c>0$, due to Basit and
Lund [BaLu19]. Over finite fields the record is: there exists $c>0$ such that
if $A \subseteq \mathbb{F}_p$ with $|A| < p^c$ then
$\max(|A+A|,|AA|) \gg |A|^{5/4+o(1)}$, due to Mohammadi and Stevens [MoSt23].
There is also a natural higher-fold generalisation
$\max(|mA|, |A^m|) \gg |A|^{m-o(1)}$ conjectured in [ErSz83] (and [Er91]) —
see Erdős problem [53] for more on that generalisation, [808] for a stronger
form of the original conjecture, and [818] for a special case. A complete
history of sum-product bounds is kept at thomasbloom.org/notes/sumproduct.html.

Problem-source citation keys on the page: [Er77c] [ErGr80] [Er91] [Er92c]
[Er95] [Er97] [Er97e] [Va99, 1.26]; remark keys: [ErSz83] [Bl25] [BaLu19]
[MoSt23].

References (entries below marked "latex/52" are recovered from the original
pipeline's WebFetch extraction of erdosproblems.com/latex/52 preserved in the
session logs — the authoritative source, though volume numbers were not
preserved; entries marked "sibling corpus" are honest stubs from repository
files sharing the key; the rest are keys only: DEFERRED):
- [ErSz83] Erdős, P. and Szemerédi, E., _On sums and products of integers_.
  Studies in pure mathematics, Birkhäuser, Basel (1983), 213–218.
  (latex/52; Birkhäuser/Basel detail from the styled sibling file.)
- [Bl25] Bloom, T. F., _Control and its applications in additive
  combinatorics_. arXiv:2501.09470 (2025). (latex/52.)
- [BaLu19] Basit, A. and Lund, B., _An improved sum-product bound for
  quaternions_. SIAM J. Discrete Math. (2019), 1044–1060. (latex/52; the page
  prose cites this for the complex-number bound.)
- [MoSt23] Mohammadi, A. and Stevens, S., _Attaining the exponent 5/4 for the
  sum-product problem in finite fields_. Int. Math. Res. Not. IMRN (2023),
  3516–3532. (latex/52.)
- [Er91] Erdős, P., _Problems and results in combinatorial analysis and
  combinatorial number theory_. Graph theory, combinatorics, and applications,
  Vol. 1 (Kalamazoo, MI, 1988) (1991), 397–406. (latex/52.)
- [Er77c] Erdős, P., _Problems and results on combinatorial number theory.
  III_. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43–72. (Sibling corpus; unverified offline.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique
  (1980). (Sibling corpus; unverified offline.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999).
  This problem: 1.26. (Sibling corpus; unverified offline.)
- [Er92c] [Er95] [Er97] [Er97e] — keys only; the corpus's expansions for these
  keys conflict: DEFERRED.

OEIS: A263996 (page and mirror agree; contents unverifiable offline).
Additional thanks to: Akshat Mudgal.
Site citation line: T. F. Bloom, Erdős Problem #52,
https://www.erdosproblems.com/52, accessed 2026-02-22.

Tags: number theory, additive combinatorics
-/

/--
**Erdős Problem #52** (The Sum-Product Conjecture) — OPEN, $250:

For every $\epsilon > 0$, there exists $c > 0$ such that for every finite set
$A$ of integers with $|A| \geq 2$,
$$\max(|A + A|, |A \cdot A|) \geq c \cdot |A|^{2 - \epsilon}.$$

A problem of Erdős and Szemerédi [ErSz83]. The current best lower bound is
$\max(|A+A|, |AA|) \gg |A|^{1270/951 - o(1)}$ due to Bloom [Bl25].

Encoding notes:
- The source has no size restriction on $A$; the guard `(A.card : ℝ) ≥ 2` is
  nevertheless **load-bearing** here because $\epsilon$ ranges over all of
  $(0, \infty)$: without it, at $\epsilon = 2$ the empty set falsifies the
  statement, since `Real.rpow 0 0 = 1` makes the right side $c \cdot 1 > 0$
  while the left side is $0$. (For every $\epsilon \neq 2$ the empty set and
  singletons are harmless.) Do not "simplify" the guard away.
- With the guard, the statement is classically equivalent to the upstream
  formal-conjectures right-hand side (`∀ ε, 0 < ε → ε < 1 → ∃ C, 0 < C ∧ ∀ A,
  max … ≥ C * |A|^(2-ε)`, no size guard): given the guarded form, take
  `C := min c 1` — cases `|A| = 0` (both sides `0` since the exponent
  `2 - ε ∈ (1,2)` is nonzero) and `|A| = 1` (left side `1 ≥ C`) are trivial;
  conversely the `ε < 1` case implies every `ε ≥ 1` case for `|A| ≥ 2` by
  monotonicity of `rpow` in the exponent (`|A|^{2-ε} ≤ |A|^{3/2}` for
  `ε ≥ 1/2`).
- `A + A` / `A * A` are Mathlib's pointwise `Finset` sumset/product set
  (self-sums $a + a$ allowed, matching the standard convention); cardinalities
  are cast to ℝ and the exponent uses `Real.rpow`.
-/
theorem erdos_52 :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ (2 - ε) :=
  sorry

/--
Variant (solved, [ErSz83]): the original Erdős–Szemerédi lower bound — there
exists a constant $\delta > 0$ (their exponent gain past $1$) and $c > 0$ such
that every finite $A \subseteq \mathbb{Z}$ with $|A| \geq 2$ satisfies
$\max(|A+A|, |AA|) \geq c \cdot |A|^{1+\delta}$.

Page-confirmed: "Erdős and Szemerédi [ErSz83] proved a lower bound of
$|A|^{1+c}$ for some constant $c > 0$."

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_52.variants.erdos_szemeredi_lower_bound :
    ∃ δ : ℝ, δ > 0 ∧ ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ (1 + δ) :=
  sorry

/--
Variant (solved, [Bl25]): the current record lower bound — for every
$\epsilon > 0$ there is $c > 0$ such that every finite $A \subseteq \mathbb{Z}$
with $|A| \geq 2$ satisfies
$\max(|A+A|, |AA|) \geq c \cdot |A|^{1270/951 - \epsilon}$.

Page-confirmed: "The current record is
$\max(|A+A|,|AA|) \gg |A|^{\frac{1270}{951}-o(1)}$ due to Bloom [Bl25]
(note $1270/951 = 1.33543\cdots$)." The $-o(1)$ in the exponent is encoded,
as usual, by the $\forall \epsilon$/$\exists c$ quantifier prefix. The
division `1270 / 951` happens in ℝ (the expected type of the `rpow` exponent),
so it is exact real division, not ℕ division.

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_52.variants.bloom_lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℤ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥
      c * (A.card : ℝ) ^ (1270 / 951 - ε) :=
  sorry

/--
Variant (solved, [ErSz83]): the Erdős–Szemerédi **upper bound**, showing the
conjectured exponent $2$ cannot be improved to $2$ itself: there is a constant
$c > 0$ and finite sets $A \subseteq \mathbb{Z}$ of arbitrarily large
cardinality with
$$\max(|A+A|, |AA|) \leq |A|^2
  \exp\left(-c\frac{\log|A|}{\log\log|A|}\right).$$

Page-confirmed: "and an upper bound of
$|A|^2\exp(-c\log|A|/\log\log|A|)$ for some constant $c>0$."

Encoding notes: "for arbitrarily large $A$" is encoded as
$\forall N, \exists A, N \leq |A|$; the auxiliary guard $3 \leq |A|$ keeps
$\log\log|A| > 0$ (for $|A| \geq 3$, $\log|A| > 1$), so the division inside
`exp` is by a positive quantity and the bound is meaningful. `exp`/`log` are
`Real.exp`/`Real.log` (in scope through the existing
`Mathlib.Analysis.SpecialFunctions.Pow.Real` import and `open Real`).

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_52.variants.erdos_szemeredi_upper_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ N : ℕ, ∃ A : Finset ℤ, N ≤ A.card ∧ 3 ≤ A.card ∧
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≤
      (A.card : ℝ) ^ (2 : ℝ) *
        exp (-(c * log (A.card : ℝ) / log (log (A.card : ℝ)))) :=
  sorry

/--
Variant (open): the same conjecture for finite sets of **real** numbers.
Page-confirmed: "There is likely nothing special about the integers in this
question, and indeed Erdős and Szemerédi also ask a similar question about
finite sets of real or complex numbers. The current best bound for sets of
reals is the same bound of Bloom above."

Stated, like the main theorem, as a direct assertion of the conjectured
affirmative direction, with the same $|A| \geq 2$ guard for the same
$\epsilon = 2$/empty-set `rpow` reason.

NOTE: this variant was added by the Fable review and is NOT compile-verified
(in particular it relies on Mathlib's `DecidableEq ℝ` instance for the
pointwise `Finset` operations; the surrounding `noncomputable section`
accommodates this).
-/
theorem erdos_52.variants.reals :
    ∀ ε : ℝ, ε > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℝ, (A.card : ℝ) ≥ 2 →
    max ((A + A).card : ℝ) ((A * A).card : ℝ) ≥ c * (A.card : ℝ) ^ (2 - ε) :=
  sorry

end
