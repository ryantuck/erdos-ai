import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped Classical
open Finset BigOperators

/--
A set A ⊆ ℕ is *sum-divisibility-free* if there are no distinct a, b, c ∈ A
with b, c > a and a ∣ (b + c).

Encoding notes:

- The hypotheses `a ≠ b` and `a ≠ c` are redundant (each is implied by the
  strict inequalities `a < b` and `a < c`); the substantive distinctness
  condition is `b ≠ c`. They are kept for readability of the "distinct
  a, b, c" reading of the source.
- Membership of `0` in `A` is harmless: with `a = 0` the divisibility
  `0 ∣ (b + c)` requires `b + c = 0`, impossible for `0 < b`; and `0` can
  never play the role of `b` or `c` (it is not `> a` for any `a : ℕ`).
  `0` is also invisible to `counting` (which starts at 1) and contributes
  `1/0 = 0` to reciprocal sums, so nothing below is affected.
-/
def SumDivFree (A : Set ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A →
    a ≠ b → a ≠ c → b ≠ c →
    a < b → a < c → ¬(a ∣ (b + c))

/-- Counting function: |A ∩ {1, …, N}| (via `Finset.Icc 1 N`, so exactly the
elements of `A` in `{1, …, N}`; `0` is never counted). -/
noncomputable def counting (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #12, Part 1
[ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97, Er97b, Er97e, Er98]:

> Let $A$ be an infinite set such that there are no distinct $a,b,c\in A$
> such that $a\mid (b+c)$ and $b,c>a$. Is there such an $A$ with
> $\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N^{1/2}}>0$?

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/12, accessed 2026-03-05; status
re-confirmed open against the teorth/erdosproblems metadata mirror,
`data/problems.yaml` entry 12, last update 2025-08-31). Asked by Erdős and
Sárközy [ErSa70]. This is a yes/no question; following this corpus's
convention for open yes/no questions (direct assertion of the affirmative,
unrefuted direction — the page records no belief either way), the theorem
asserts existence. `liminf > 0` is unfolded to its equivalent
"∃ ε > 0 with the ratio eventually ≥ ε".

Known partial results and remarks from the problem page:

- Erdős and Sárközy [ErSa70] proved that such an $A$ must have density $0$
  (see `erdos_problem_12.variants.erdos_sarkozy_density_zero`), and that
  this is essentially best possible: for any $f(x)\to\infty$ there is such
  an $A$ with $\lvert A\cap\{1,\ldots,N\}\rvert > N/f(N)$ for infinitely
  many $N$ (see `erdos_problem_12.variants.erdos_sarkozy_best_possible`;
  their example: all integers in $(y_i, \tfrac{3}{2}y_i)$ congruent to $1$
  modulo $(2y_{i-1})!$, for a sufficiently quickly growing sequence $y_i$).
- An example of such an $A$ with
  $\liminf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N^{1/2}}\log N > 0$ is
  the set of $p^2$ with $p \equiv 3 \pmod 4$ prime. (Not formalized here:
  `Nat.Prime` is not among this file's imports; recorded as deferred
  enrichment.)
- Elsholtz and Planitzer [ElPl17] constructed such an $A$ with
  $\lvert A\cap\{1,\ldots,N\}\rvert \gg
  N^{1/2}/((\log N)^{1/2}(\log\log N)^2(\log\log\log N)^2)$.
- Schoen [Sc01] proved that if all elements of $A$ are pairwise coprime
  then $\lvert A\cap\{1,\ldots,N\}\rvert \ll N^{2/3}$ for infinitely many
  $N$ (see `erdos_problem_12.variants.schoen`); Baier [Ba04] improved this
  to $\ll N^{2/3}/\log N$ (see `erdos_problem_12.variants.baier`).

For the finite version see Erdős Problem #13. Tag: number theory. The page
links an upstream formalization (google-deepmind/formal-conjectures,
`ErdosProblems/12.lean`).

References (the `erdosproblems.com/latex/12` bibliography was not
recoverable offline; entries below are assembled from sibling files in this
corpus and from the page's prose, are honest stubs where noted, and omit
journal/volume/page data rather than guess it):

- [ErSa70] Erdős, P. and Sárközy, A. (1970). (Stub: authors from the page
  prose "Asked by Erdős and Sárközy [ErSa70]"; year per key convention.)
- [Er73] Erdős, P., Problems and results on combinatorial number theory.
  A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State
  Univ., Fort Collins, Colo., 1971) (1973), 117-138.
- [Er75b] Erdős, P. (1975). (Stub: sibling files disagree on this key's
  title — "Problems and results in combinatorial number theory", Journées
  arithmétiques, vs "Problems and results on combinatorial number theory
  II/III".)
- [Er77c] Erdős, P., Problems and results on combinatorial number theory.
  III. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43-72.
- [Er92c] Erdős, P. (1992). (Stub: sibling files disagree on this key's
  title — "Some of my favourite problems in various branches of
  combinatorics", Matematiche (Catania) (1992), vs "Some of my forgotten
  problems in number theory", Hardy-Ramanujan J. (1992).)
- [Er95c] Erdős, P. (1995). (Stub: sibling files disagree on this key's
  title — "Some problems in number theory", Octogon Math. Mag. (1995), 3-5,
  vs "Some of my favourite problems which recently have been solved".)
- [Er97] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory (1997). (Corpus-unanimous title for this key,
  but it coincides with the corpus title of [Er98] below — a possible
  corpus-level conflation, unresolved offline.)
- [Er97b] Erdős, P. (1997). (Stub: sibling files disagree on this key's
  contents.)
- [Er97e] Erdős, P. (1997). (Stub: sibling files disagree on this key's
  title.)
- [Er98] Erdős, P., Some of my new and almost new problems and results in
  combinatorial number theory. Number theory (Eger, 1996) (1998), 169-180.
- [ElPl17] Elsholtz, C. and Planitzer, S. (2017). (Stub: surnames from the
  page prose; year per key convention.)
- [Sc01] Schoen (2001). (Stub: surname from the page prose; year per key
  convention.)
- [Ba04] Baier (2004). (Stub: surname from the page prose; year per key
  convention.)
-/
theorem erdos_problem_12a :
    ∃ A : Set ℕ, A.Infinite ∧ SumDivFree A ∧
      ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ε ≤ (counting A N : ℝ) / Real.sqrt (N : ℝ) :=
  sorry

/--
Erdős Problem #12, Part 2
[ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97, Er97b, Er97e, Er98]:

> Does there exist some absolute constant $c>0$ such that there are always
> infinitely many $N$ with
> $\lvert A\cap\{1,\ldots,N\}\rvert < N^{1-c}$?

("always" = for every infinite sum-divisibility-free $A$; the constant $c$
is absolute, i.e. quantified outside $A$.) **Status: OPEN**; a yes/no
question, asserted here in the affirmative direction per the corpus
convention (see `erdos_problem_12a`'s docstring for the status and
convention provenance). "Infinitely many $N$" is encoded as "arbitrarily
large $N$" (`∀ M, ∃ N ≥ M`). Schoen's and Baier's results (see
`erdos_problem_12.variants.schoen` / `.baier`) prove exactly this shape of
conclusion, with exponent $2/3$, under the extra hypothesis of pairwise
coprimality.
-/
theorem erdos_problem_12b :
    ∃ c : ℝ, 0 < c ∧
      ∀ A : Set ℕ, A.Infinite → SumDivFree A →
        ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
          (counting A N : ℝ) < (N : ℝ) ^ ((1 : ℝ) - c) :=
  sorry

/--
Erdős Problem #12, Part 3
[ErSa70, Er73, Er75b, Er77c, Er92c, Er95c, Er97, Er97b, Er97e, Er98]:

> Is it true that $\sum_{n\in A}\frac{1}{n}<\infty$?

(for every infinite sum-divisibility-free $A$). **Status: OPEN**; a yes/no
question, asserted here in the affirmative direction per the corpus
convention (see `erdos_problem_12a`'s docstring). Convergence of the series
of non-negative terms is encoded as boundedness of all finite partial sums,
which is equivalent to summability; if `0 ∈ A` its term is `1/0 = 0` in
Lean and harmless.
-/
theorem erdos_problem_12c
    (A : Set ℕ)
    (hInf : A.Infinite)
    (hA : SumDivFree A) :
    ∃ M : ℝ, ∀ F : Finset ℕ, (↑F : Set ℕ) ⊆ A →
      ∑ n ∈ F, (1 : ℝ) / (n : ℝ) ≤ M :=
  sorry

/--
Erdős Problem #12, Erdős–Sárközy density theorem (SOLVED) [ErSa70]:

every infinite sum-divisibility-free set $A$ has density $0$, i.e.
$\lvert A\cap\{1,\ldots,N\}\rvert/N \to 0$, encoded as: for every
$\varepsilon > 0$, eventually
$\lvert A\cap\{1,\ldots,N\}\rvert < \varepsilon N$.
-/
theorem erdos_problem_12.variants.erdos_sarkozy_density_zero
    (A : Set ℕ)
    (hInf : A.Infinite)
    (hA : SumDivFree A) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (counting A N : ℝ) < ε * (N : ℝ) :=
  sorry

/--
Erdős Problem #12, Erdős–Sárközy "essentially best possible" theorem
(SOLVED) [ErSa70]:

the density-$0$ theorem is essentially best possible: given any function
$f(x)\to\infty$ there exists an infinite sum-divisibility-free set $A$ with
$\lvert A\cap\{1,\ldots,N\}\rvert > N/f(N)$ for infinitely many $N$. (Their
example: all integers in $(y_i, \tfrac{3}{2}y_i)$ congruent to $1$ modulo
$(2y_{i-1})!$, where $y_i$ grows sufficiently quickly.) The hypothesis
`0 < f n` is a harmless normalization: the page's $f(x)\to\infty$ makes $f$
eventually positive, and only arbitrarily large $N$ matter for the
conclusion, so restricting to everywhere-positive $f$ loses no content and
keeps the real division `N / f N` well-behaved.
-/
theorem erdos_problem_12.variants.erdos_sarkozy_best_possible
    (f : ℕ → ℝ)
    (hf_pos : ∀ n : ℕ, 0 < f n)
    (hf : ∀ C : ℝ, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → C ≤ f n) :
    ∃ A : Set ℕ, A.Infinite ∧ SumDivFree A ∧
      ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ (N : ℝ) / f N < (counting A N : ℝ) :=
  sorry

/--
Erdős Problem #12, Schoen's theorem (SOLVED) [Sc01]:

if all elements of an infinite sum-divisibility-free set $A$ are pairwise
coprime, then $\lvert A\cap\{1,\ldots,N\}\rvert \ll N^{2/3}$ for infinitely
many $N$. The Vinogradov bound with "for infinitely many $N$" is encoded as
$\exists C > 0$ with $\lvert A\cap\{1,\ldots,N\}\rvert \le C\,N^{2/3}$ for
arbitrarily large $N$. (Pairwise coprimality is spelled with core
`Nat.gcd`; note the upstream formal-conjectures file states this bound as
`=O[atTop]`, i.e. for *all* large $N$ — stronger than the page's
"for infinitely many $N$", which is what is encoded here.)
-/
theorem erdos_problem_12.variants.schoen
    (A : Set ℕ)
    (hInf : A.Infinite)
    (hA : SumDivFree A)
    (hcop : ∀ m ∈ A, ∀ n ∈ A, m ≠ n → Nat.gcd m n = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (counting A N : ℝ) ≤ C * (N : ℝ) ^ ((2 : ℝ) / 3) :=
  sorry

/--
Erdős Problem #12, Baier's improvement of Schoen's theorem (SOLVED) [Ba04]:

under the same hypotheses as `erdos_problem_12.variants.schoen`, the bound
improves to $\lvert A\cap\{1,\ldots,N\}\rvert \ll N^{2/3}/\log N$ for
infinitely many $N$. (At $N = 1$ the right-hand side is
$C \cdot 1/\log 1 = 0$ by Lean's convention `x/0 = 0`; this affects nothing
since the conclusion only concerns arbitrarily large $N$. Same
"infinitely many $N$" encoding caveat versus the upstream `=O[atTop]` form
as in the Schoen variant.)
-/
theorem erdos_problem_12.variants.baier
    (A : Set ℕ)
    (hInf : A.Infinite)
    (hA : SumDivFree A)
    (hcop : ∀ m ∈ A, ∀ n ∈ A, m ≠ n → Nat.gcd m n = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      (counting A N : ℝ) ≤ C * (N : ℝ) ^ ((2 : ℝ) / 3) / Real.log (N : ℝ) :=
  sorry
