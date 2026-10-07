-- [AI - Claude Sonnet 5.5]: Erdős Problem 121 — second-pass formalization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators Topology
open Filter

/-!
# Erdős Problem #121: Square-Free Product Sets

*Source:* [erdosproblems.com/121](https://www.erdosproblems.com/121) (status **DISPROVED**:
"This has been solved in the negative."; captured 2026-02-20 as the tidied problem box).
[Er94b] [Er97] [Er97e] [Er98]

Let $F_{k}(N)$ be the size of the largest $A\subseteq \{1,\ldots,N\}$ such that the product of
no $k$ many distinct elements of $A$ is a square. Is $F_5(N)=(1-o(1))N$? More generally, is
$F_{2k+1}(N)=(1-o(1))N$?

Remarks recorded on the page:
* Conjectured by Erdős, Sós, and Sárközy [ESS95], who proved
  $F_2(N)=\left(\frac{6}{\pi^2}+o(1)\right)N$, $F_3(N) = (1-o(1))N$, and also established
  asymptotics for $F_k(N)$ for all even $k\geq 4$ (in particular $F_k(N)\asymp N/\log N$ for
  all even $k\geq 4$). Erdős [Er38] earlier proved that $F_4(N)=o(N)$ - indeed, if
  $\lvert A\rvert \gg N$ and $A\subseteq \{1,\ldots,N\}$ then there is a non-trivial solution
  to $ab=cd$ with $a,b,c,d\in A$.
* Erdős (and independently Hall [Ha96] and Montgomery) also asked about $F(N)$, the size of the
  largest $A\subseteq\{1,\ldots,N\}$ such that the product of no odd number of $a\in A$ is a
  square. Ruzsa [Ru77] observed that $1/2<\lim F(N)/N <1$. Granville and Soundararajan
  [GrSo01] proved an asymptotic $F(N)=(1-c+o(1))N$ where $c=0.1715\ldots$ is an explicit
  constant.
* This problem was answered in the negative by Tao [Ta24], who proved that for any
  $k\geq 4$ there is some constant $c_k>0$ such that $F_k(N) \leq (1-c_k+o(1))N$.
* See also Problem #888.

Tags: number theory, squares.

**Form of the statements.** The page's questions are yes/no, and both answers are no.
`erdos_problem_121` is Tao's theorem, as in the first pass and byte for byte. It is stronger
than the two negations: it covers every $k \ge 4$, even $k$ included, and gives a uniform gap.
The literal negations are `erdos_problem_121.variants.not_five` and
`erdos_problem_121.variants.not_odd`. "More generally" is read for $k \ge 2$, because
$F_3(N) = (1-o(1))N$ is a theorem [ESS95] (`variants.three`).

**Encoding.**
* "$F_k(N) = (1-o(1))N$" is `Tendsto (F k N / N) atTop (𝓝 1)`. Since $F_k(N) \le N$, this is
  equivalent to $F_k(N) \ge (1-\varepsilon)N$ eventually, for every $\varepsilon > 0$.
* `F k N` is a genuine maximum. The defining set contains $0$ (take $A = \emptyset$, which is
  vacuous for $k \ge 1$) and is bounded by $N$. For $k = 0$ the empty product $1$ is a square,
  so no set qualifies and `F 0 N = 0`. The theorems avoid $k = 0$.
* The first pass's `noKSquareProduct` and `F` are unchanged. Elements are drawn from
  `Finset.Icc 1 N`, so every product is positive.

## References

* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.
* [Er97] Erdős, P., _Problems in number theory_. New Zealand J. Math. (1997), 155–160.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537.
* [Er98] Erdős, P., _Some of my new and almost new problems and results in combinatorial number
  theory_. Number theory (Eger, 1996) (1998), 169–180.
* [ESS95] Erdős, P., Sárközy, A. and Sós, V. T., _On product representations of powers. I_.
  European J. Combin. (1995), 567–588.
* [Er38] Erdős, P., _On sequences of integers no one of which divides the product of two others
  and on related problems_. Tomsk. Gos. Univ. Ucen Zap. (1938), 74–82.
* [GrSo01] Granville, A. and Soundararajan, K., _The spectrum of multiplicative functions_.
  Ann. of Math. (2) (2001), 407–470.
* [Ha96] Hall, R. R., _Proof of a conjecture of Heath-Brown concerning quadratic residues_.
  Proc. Edinburgh Math. Soc. (2) (1996), 581–588.
* [Ru77] Ruzsa, I. Z., _General multiplicative functions_. Acta Arith. (1977), 313–347.
* [Ta24] Tao, T., _On product representations of squares_. arXiv:2405.11610 (2024).

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/121` for [ESS95], [Er38],
[GrSo01], [Ha96], [Ru77] and [Ta24]. [Er94b], [Er98] and [Er97e]'s title also appear in sibling
`/latex` extractions. [Er97] and the venues of [Er97e] are from upstream `121.lean`.)
-/

/-- A finset A has the property that no k distinct elements have a product that is
    a perfect square. -/
def noKSquareProduct (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → B.card = k → ¬IsSquare (∏ b ∈ B, b)

/-- F k N is the size of the largest subset A of {1, ..., N} such that
    no k distinct elements of A have a product that is a perfect square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ noKSquareProduct k A}

/--
Erdős Problem #121 [Er94b, Er97, Er97e, Er98] — DISPROVED

Let F_k(N) be the size of the largest A ⊆ {1,...,N} such that the product of no k
distinct elements of A is a perfect square.

Conjectured by Erdős, Sós, and Sárközy [ESS95]: Is F_5(N) = (1 - o(1)) N?
More generally, is F_{2k+1}(N) = (1 - o(1)) N for all k ≥ 2?

Background:
  - Erdős–Sós–Sárközy [ESS95] proved F_2(N) = (6/π² + o(1)) N and F_3(N) = (1 - o(1)) N,
    and F_k(N) ≍ N / log N for all even k ≥ 4.
  - Erdős [Er38] proved F_4(N) = o(N) (in particular, density 0 for k = 4).

This was answered in the NEGATIVE by Tao [Ta24], who proved that for any k ≥ 4 there
exists a constant c_k > 0 such that F_k(N) ≤ (1 - c_k + o(1)) N. Thus the density of
the largest such set is bounded strictly away from 1 for all k ≥ 4, disproving the
conjecture for all odd k ≥ 5.

The theorem below formalizes Tao's result. It implies the literal negative answers, which are
`erdos_problem_121.variants.not_five` and `erdos_problem_121.variants.not_odd`.
-/
theorem erdos_problem_121 :
    ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c + ε) * N :=
  sorry

/--
The first question, answered no (PROVED; a consequence of Tao [Ta24] with k = 5):
$F_5(N) = (1-o(1))N$ is false.
-/
theorem erdos_problem_121.variants.not_five :
    ¬ Tendsto (fun N : ℕ => (F 5 N : ℝ) / N) atTop (𝓝 1) :=
  sorry

/--
The general question, answered no (PROVED; a consequence of Tao [Ta24]): it is not the case that
$F_{2k+1}(N) = (1-o(1))N$ for every $k \ge 2$.
-/
theorem erdos_problem_121.variants.not_odd :
    ¬ ∀ k : ℕ, 2 ≤ k → Tendsto (fun N : ℕ => (F (2 * k + 1) N : ℝ) / N) atTop (𝓝 1) :=
  sorry

/--
Erdős, Sós and Sárközy [ESS95] (PROVED): $F_3(N) = (1-o(1))N$. So the conjecture does hold for
$k = 1$, and the question starts at $k = 2$.
-/
theorem erdos_problem_121.variants.three :
    Tendsto (fun N : ℕ => (F 3 N : ℝ) / N) atTop (𝓝 1) :=
  sorry

/--
Erdős, Sós and Sárközy [ESS95] (PROVED): $F_2(N) = (6/\pi^2 + o(1))N$.
-/
theorem erdos_problem_121.variants.two :
    Tendsto (fun N : ℕ => (F 2 N : ℝ) / N) atTop (𝓝 (6 / Real.pi ^ 2)) :=
  sorry

/--
Erdős [Er38] (PROVED): $F_4(N) = o(N)$.
-/
theorem erdos_problem_121.variants.four :
    Tendsto (fun N : ℕ => (F 4 N : ℝ) / N) atTop (𝓝 0) :=
  sorry

/--
Erdős, Sós and Sárközy [ESS95] (PROVED): $F_k(N) \asymp N/\log N$ for every even $k \ge 4$.
-/
theorem erdos_problem_121.variants.even_k :
    ∀ k : ℕ, 4 ≤ k → Even k →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
        c * N / Real.log N ≤ (F k N : ℝ) ∧ (F k N : ℝ) ≤ C * N / Real.log N :=
  sorry

/-- A finset A has the property that the product of no odd number of its elements is a perfect
    square. That is, every sub-finset of odd cardinality has a non-square product. -/
def oddProductFree (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬IsSquare (∏ b ∈ B, b)

/-- Fodd N is the size of the largest subset A of {1, ..., N} such that the product of no odd
    number of elements of A is a perfect square. This is the page's function F(N). -/
noncomputable def Fodd (N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ oddProductFree A}

/--
Ruzsa [Ru77] and Granville–Soundararajan [GrSo01] (PROVED): for the function counting sets with no
odd-size square product, $F(N) = (1-c+o(1))N$ for an explicit constant $c$, and $1/2 < 1-c < 1$.
The page gives $c = 0.1715\ldots$. That numeric value is not asserted here, because its digits
were not verified.
-/
theorem erdos_problem_121.variants.odd_number_of_factors :
    ∃ c : ℝ, 0 < c ∧ c < 1 / 2 ∧
      Tendsto (fun N : ℕ => (Fodd N : ℝ) / N) atTop (𝓝 (1 - c)) :=
  sorry
