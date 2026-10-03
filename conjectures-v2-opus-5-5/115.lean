-- [AI - Claude Opus 5.5]: Erdős Problem 115 — second-pass formalization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Connected.Basic

open Polynomial

/-!
# Erdős Problem #115: The Derivative of a Polynomial on a Connected Lemniscate

*Source:* [erdosproblems.com/115](https://www.erdosproblems.com/115) (status **PROVED**: "This
has been solved in the affirmative."; captured 2026-02-19 as the tidied problem box).
[Er61, p.246] [Er90]

If $p(z)$ is a polynomial of degree $n$ such that $\{z : \lvert p(z)\rvert\leq 1\}$ is connected
then is it true that
$$\max_{\substack{z\in\mathbb{C}\\ \lvert p(z)\rvert\leq 1}} \lvert p'(z)\rvert \leq
(\tfrac{1}{2}+o(1))n^2?$$

Remarks recorded on the page:
* The lower bound is easy: this is $\geq n$ and equality holds if and only if $p(z)=z^n$. The
  assumption that the set is connected is necessary, as witnessed for example by
  $p(z)=z^2+10z+1$.
* The Chebyshev polynomials show that $n^2/2$ is best possible here. Erdős originally
  conjectured this without the $o(1)$ term but Szabados observed that was too strong.
  Pommerenke [Po59a] proved an upper bound of $\frac{e}{2}n^2$.
* Eremenko and Lempert [ErLe94] have shown this is true, and in fact Chebyshev polynomials are
  the extreme examples.

**Normalisation: `p` is monic.** The page does not say so, but the problem is false without
it.
* `max |p'|` over the lemniscate is not scale-invariant. For $p = a z^n$ the lemniscate is the
  disc of radius $|a|^{-1/n}$, on which $\max |p'| = n |a|^{1/n}$, and this is unbounded.
* The Chebyshev polynomial $T_n$ itself has a connected lemniscate, since its critical values
  are $\pm 1$, but $T_n'(1) = n^2$.
* The page's remarks only make sense for monic $p$: the lower bound $n$, and the sharpness of
  $1/2$ via Chebyshev polynomials. Those polynomials must be rescaled to be monic:
  $q(z) = T_n(z/\lambda)$ with $\lambda = 2^{(n-1)/n}$. Then
  $|q'(\lambda)| = n^2/\lambda = 2^{1/n}\,n^2/2$.
* The first pass omitted the hypothesis, and its statement is false; see
  `erdos_problem_115.variants.without_monic_false`. Upstream (`erdos_115`) also assumes
  `p.Monic`.

**Status.** The page banner reads PROVED. The mirror records `proved (Lean)` (2026-03-03), and
upstream links a formal proof.

Tags: polynomials, analysis.

## References

* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Po59a] Pommerenke, Ch., _On the derivative of a polynomial_. Michigan Math. J. (1959),
  373–375.
* [ErLe94] Eremenko, A. and Lempert, L., _An extremal problem for polynomials_. Proc. Amer.
  Math. Soc. (1994), 191–193.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/115` for [Po59a] and
[ErLe94]. Sibling `/latex` extractions for [Er61] and [Er90], which agree with upstream
`115.lean`.)
-/

/-- The lemniscate of a complex polynomial p: the sublevel set {z ∈ ℂ : |p(z)| ≤ 1}. -/
def lemniscate (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ ≤ 1}

/--
Erdős Conjecture (Problem #115) [Er61, Er90], proved by Eremenko–Lempert [ErLe94]:

If p(z) is a monic polynomial of degree n such that {z ∈ ℂ : |p(z)| ≤ 1} is connected,
then
  max { |p'(z)| : z ∈ ℂ, |p(z)| ≤ 1 } ≤ (1/2 + o(1)) n².

That is, for every ε > 0 there exists N such that for all n ≥ N, every monic polynomial
p of degree n whose lemniscate is connected satisfies |p'(z)| ≤ (1/2 + ε) n² for
all z in the lemniscate.

The Chebyshev polynomials, rescaled to be monic, show that the constant 1/2 is sharp. Erdős
originally conjectured the bound n²/2 exactly (without the o(1)), but Szabados observed that
the stronger form fails. Pommerenke [Po59a] proved the weaker bound (e/2) n².
-/
theorem erdos_problem_115 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected (lemniscate p) →
      ∀ z : ℂ, z ∈ lemniscate p →
        ‖(derivative p).eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2 :=
  sorry

/--
The first-pass statement, without `p.Monic`, is false (PROVED). The Chebyshev polynomial T_n has
a connected lemniscate, since its critical values are ±1, and T_n(1) = 1 but T_n'(1) = n². So
for ε < 1/2 the bound fails for every n ≥ 1.
-/
theorem erdos_problem_115.variants.without_monic_false :
    ¬ (∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.natDegree = n →
      IsConnected (lemniscate p) →
      ∀ z : ℂ, z ∈ lemniscate p →
        ‖(derivative p).eval z‖ ≤ (1 / 2 + ε) * (n : ℝ) ^ 2) :=
  sorry

/--
Pommerenke [Po59a] (PROVED): for every n ≥ 1 and every monic p of degree n with connected
lemniscate, |p'(z)| ≤ (e/2) n² on the lemniscate.
-/
theorem erdos_problem_115.variants.pommerenke :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected (lemniscate p) →
      ∀ z : ℂ, z ∈ lemniscate p →
        ‖(derivative p).eval z‖ ≤ Real.exp 1 / 2 * (n : ℝ) ^ 2 :=
  sorry

/--
Sharpness, and failure of the exact bound n²/2 (PROVED; Chebyshev polynomials and Szabados's
observation). For every n ≥ 1, q(z) = T_n(z/λ) with λ = 2^{(n-1)/n} is monic, with connected
lemniscate containing λ, and |q'(λ)| = 2^{1/n} n²/2 > n²/2.
-/
theorem erdos_problem_115.variants.chebyshev_sharpness :
    ∀ n : ℕ, 1 ≤ n →
    ∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = n ∧ IsConnected (lemniscate p) ∧
      ∃ z : ℂ, z ∈ lemniscate p ∧ (n : ℝ) ^ 2 / 2 < ‖(derivative p).eval z‖ :=
  sorry

/--
The easy lower bound (PROVED): the maximum is at least n. Equality holds exactly for
p(z) = (z - c)^n. The page says "p(z) = z^n", which is the same up to translation.
-/
theorem erdos_problem_115.variants.lower_bound :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected (lemniscate p) →
      ∃ z : ℂ, z ∈ lemniscate p ∧ (n : ℝ) ≤ ‖(derivative p).eval z‖ :=
  sorry

/--
Connectedness is necessary (PROVED). Without it, |p'| on the lemniscate is unbounded in every
degree n ≥ 2. For example, take p(z) = z^{n-1}(z - b) and z = b, so that p'(b) = b^{n-1}. For
the page's example p(z) = z² + 10z + 1, |p'| = 2√24 > 2 = n²/2 at either root.
-/
theorem erdos_problem_115.variants.connectedness_needed :
    ∀ n : ℕ, 2 ≤ n → ∀ C : ℝ,
    ∃ p : Polynomial ℂ, p.Monic ∧ p.natDegree = n ∧
      ∃ z : ℂ, z ∈ lemniscate p ∧ C < ‖(derivative p).eval z‖ :=
  sorry
