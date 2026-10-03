-- [AI - Claude Opus 5.5]: Erdős Problem 119 — second-pass formalization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex Finset BigOperators

/-!
# Erdős Problem #119: Maximum Modulus of Products over a Unimodular Sequence

*Source:* [erdosproblems.com/119](https://www.erdosproblems.com/119) (status **OPEN** when
captured: "This is open, and cannot be resolved with a finite computation."; prize \$100;
captured 2026-02-20 and 2026-03-05 as the tidied problem box). [Er57] [Er61] [Er64b] [Ha74]
[Er82e] [Er90] [Er97f] [Va99, 2.38]

Let $z_i$ be an infinite sequence of complex numbers such that $\lvert z_i\rvert=1$ for all
$i\geq 1$, and for $n\geq 1$ let $p_n(z)=\prod_{i\leq n} (z-z_i)$. Let
$M_n=\max_{\lvert z\rvert=1}\lvert p_n(z)\rvert$.

Is it true that $\limsup M_n=\infty$?

Is it true that there exists $c>0$ such that for infinitely many $n$ we have $M_n > n^c$?

Is it true that there exists $c>0$ such that, for all large $n$,
$\sum_{k\leq n}M_k > n^{1+c}$?

Remarks recorded on the page:
* This is Problem 4.1 in [Ha74] where it is attributed to Erdős.
* The weaker conjecture that $\limsup M_n=\infty$ was proved by Wagner [Wa80], who showed that
  there is some $c>0$ with $M_n>(\log n)^c$ infinitely often.
* The second question was answered by Beck [Be91], who proved that there exists some $c>0$
  such that $\max_{n\leq N} M_n > N^c$. Erdős (e.g. see [Ha74]) gave a construction of a
  sequence with $M_n\leq n+1$ for all $n$. Linden [Li77] improved this to give a sequence
  with $M_n\ll n^{1-c}$ for some $c>0$.
* The third question seems to remain open.

**Status after capture.** The site owner's mirror changed the problem from `open` to
`solved` in commit `cfe07e4` (2026-07-19), and to `solved (Lean)` in `dfbf467`
(2026-08-23). Upstream `erdos_119.parts.iii` (`df3f12d`) is `answer(True)`. Its docstring
credits GPT 5.6 and Korsky with $\sum_{k\le n} M_k \gg n^{5/4}/\sqrt{\log n}$, and links a
formal proof. This second-pass review has not checked that result. All three statements
below assert the asked ("yes") direction, which is correct whether part (iii) is open or
solved affirmatively.

**Encoding.**
* The sequence is 0-indexed: `z_seq i` is $z_{i+1}$. `maxModulus z_seq k` is the page's
  $M_k$ for $k \ge 1$, and $M_0 = 1$ is the empty product.
* The sum in `erdos_problem_119c` includes $M_0 = 1$, which is harmless asymptotically.
* `maxModulus` is a real `iSup`. Off the circle the inner supremum is `sSup ∅ = 0`. The
  function is bounded by $2^n$, so the `iSup` is the true maximum.
* Parts (ii) and (iii) take $c$ uniform over all sequences ($\exists c\ \forall z$). That is
  stronger than the literal reading, in which $c$ may depend on the sequence. Beck's $c$ is
  uniform. The per-sequence readings are the variants `part_ii_as_asked` and
  `part_iii_per_sequence`.

Tags: analysis, polynomials.

## References

* [Er57] Erdős, P., _Some unsolved problems_. Michigan Math. J. (1957), 291–300.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Er64b] Erdős, P., _Problems and results on diophantine approximations_. Compositio Math.
  (1964), 52–65.
* [Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), 155–180.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982),
  59–79.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. (Problem 2.38.)
* [Wa80] Wagner, G., _On a problem of Erdős in Diophantine approximation_. Bull. London Math.
  Soc. (1980), 81–88.
* [Li77] Linden, C. N., _The modulus of polynomials with zeros on the unit circle_. Bull.
  London Math. Soc. (1977), 65–69.
* [Be91] Beck, J., _The modulus of polynomials with zeros on the unit circle: A problem of
  Erdős_. Annals of Math. (1991), 609–651.

(Provenance: no `/latex/119` fetch exists in the session logs. [Wa80], [Li77] and [Be91] are
from upstream `119.lean`. The others are from sibling `/latex` extractions, which agree with
upstream.)
-/

noncomputable section

/--
The product polynomial p_n(z) = ∏_{i<n} (z - z_i) for a sequence on the unit circle.
-/
def prodPoly (z_seq : ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∏ i ∈ range n, (z - z_seq i)

/--
M_n = sup_{|z|=1} |p_n(z)|, the maximum modulus of p_n on the unit circle.
-/
def maxModulus (z_seq : ℕ → ℂ) (n : ℕ) : ℝ :=
  ⨆ (z : ℂ) (_ : ‖z‖ = 1), ‖prodPoly z_seq n z‖

/--
Erdős Problem #119 (part 1) - Proved by Wagner [Wa80]:

For any sequence z_i on the unit circle, limsup M_n = ∞.
Equivalently, M_n is unbounded.
-/
theorem erdos_problem_119a :
    ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
      ∀ B : ℝ, ∃ n : ℕ, maxModulus z_seq n > B :=
  sorry

/--
Erdős Problem #119 (part 2) - Proved by Beck [Be91], in Beck's form:

There exists c > 0 such that for any sequence z_i on the unit circle,
max_{n ≤ N} M_n > N^c.

This implies the question as asked: M_n > n^c for infinitely many n. See
`erdos_problem_119.variants.part_ii_as_asked`.
-/
theorem erdos_problem_119b :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
        ∀ N : ℕ, 0 < N →
          ∃ n : ℕ, n ≤ N ∧ maxModulus z_seq n > (N : ℝ) ^ c :=
  sorry

/--
Erdős Problem #119 (part 3) - \$100. OPEN on the page when captured; recorded as solved in the
mirror since 2026-07-19 (see the module docstring):

There exists c > 0 such that for any sequence z_i on the unit circle
and all sufficiently large n, ∑_{k ≤ n} M_k > n^{1+c}.
-/
theorem erdos_problem_119c :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          ∑ k ∈ range (n + 1), maxModulus z_seq k > (n : ℝ) ^ (1 + c) :=
  sorry

/--
Question (ii) as literally asked (PROVED; implied by `erdos_problem_119b`). For every unimodular
sequence there is c > 0 with M_n > n^c for infinitely many n.
-/
theorem erdos_problem_119.variants.part_ii_as_asked :
    ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
      ∃ c : ℝ, 0 < c ∧ {n : ℕ | (n : ℝ) ^ c < maxModulus z_seq n}.Infinite :=
  sorry

/--
Question (iii) with c allowed to depend on the sequence (SOLVED per the mirror; implied by
`erdos_problem_119c`). This is upstream's reading.
-/
theorem erdos_problem_119.variants.part_iii_per_sequence :
    ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        ∑ k ∈ range (n + 1), maxModulus z_seq k > (n : ℝ) ^ (1 + c) :=
  sorry

/--
Wagner [Wa80] (PROVED): there is c > 0 such that, for every unimodular sequence,
M_n > (log n)^c for infinitely many n.
-/
theorem erdos_problem_119.variants.wagner :
    ∃ c : ℝ, 0 < c ∧
      ∀ (z_seq : ℕ → ℂ), (∀ i, ‖z_seq i‖ = 1) →
        {n : ℕ | Real.log n ^ c < maxModulus z_seq n}.Infinite :=
  sorry

/--
Erdős's construction (PROVED; see [Ha74]): some unimodular sequence has M_n ≤ n + 1 for all n.
-/
theorem erdos_problem_119.variants.erdos_construction :
    ∃ z_seq : ℕ → ℂ, (∀ i, ‖z_seq i‖ = 1) ∧
      ∀ n : ℕ, maxModulus z_seq n ≤ n + 1 :=
  sorry

/--
Linden [Li77] (PROVED): some unimodular sequence has M_n ≪ n^{1-c} for some c > 0.
-/
theorem erdos_problem_119.variants.linden :
    ∃ z_seq : ℕ → ℂ, (∀ i, ‖z_seq i‖ = 1) ∧
      ∃ c C : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → maxModulus z_seq n ≤ C * (n : ℝ) ^ (1 - c) :=
  sorry

end
