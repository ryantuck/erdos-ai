-- [AI - Claude Opus 5.5]: Erdős Problem 114 — second-pass formalization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Hausdorff

open scoped ENNReal
open Polynomial MeasureTheory

/-!
# Erdős Problem #114: The Erdős–Herzog–Piranian Lemniscate Problem

*Source:* [erdosproblems.com/114](https://www.erdosproblems.com/114) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; prize \$250; captured 2026-02-19
as the tidied problem box). [EHP58, p.142] [Er61, p.247] [Ha74] [Er82e] [Er90] [Er97f]
[Va99, 2.35]

If $p(z)\in\mathbb{C}[z]$ is a monic polynomial of degree $n$ then is the length of the curve
$\{ z\in \mathbb{C} : \lvert p(z)\rvert=1\}$ maximised when $p(z)=z^n-1$?

Remarks recorded on the page:
* A problem of Erdős, Herzog, and Piranian [EHP58]. It is also listed as Problem 4.10 in
  [Ha74], where it is attributed to Erdős.
* In [Va99] it is just asked whether the length is at most $2n+O(1)$. This is true, as a
  consequence of the result of Tao [Ta25] below.
* Let the maximal length of such a curve be denoted by $f(n)$. The length of the curve when
  $p(z)=z^n-1$ is $2n+O(1)$, and hence the conjecture implies in particular that
  $f(n)=2n+O(1)$.
* Dolzhenko [Do61] proved $f(n) \leq 4\pi n$, but few were aware of this work. Pommerenke
  [Po61] proved $f(n)\ll n^2$. Borwein [Bo95] proved $f(n)\ll n$, unaware of Dolzhenko's
  earlier work. The prize of \$250 is reported by Borwein [Bo95].
* Eremenko and Hayman [ErHa99] proved the full conjecture when $n=2$, and $f(n)\leq 9.173n$
  for all $n$.
* Danchenko [Da07] proved $f(n)\leq 2\pi n$.
* Fryntov and Nazarov [FrNa09] proved that $z^n-1$ is a local maximiser, and solved this
  problem asymptotically, proving that $f(n)\leq 2n+O(n^{7/8})$.
* Tao [Ta25] has proved that $p(z)=z^n-1$ is the unique (up to rotation and translation)
  maximiser for all sufficiently large $n$.
* Erdős, Herzog, and Piranian [EHP58] also ask whether the length is at least $2\pi$ if
  $\{ z: \lvert f(z)\rvert<1\}$ is connected (which $z^n$ shows is the best possible). This
  was proved by Pommerenke [Po59].

**Encoding.** Length is the 1-dimensional Hausdorff measure `μH[1]`. Mathlib does not
normalise it, so for $d = 1$ it gives a segment its length. Both sides are finite: by [Da07]
every such lemniscate has length at most $2\pi n$. The hypothesis $n \ge 1$ is needed, because
for $n = 0$ the only monic polynomial is $1$, whose level set is all of $\mathbb{C}$.

**Status.** The page banner reads OPEN. The mirror records `falsifiable` (2025-12-28), which
is also unresolved. By [ErHa99] and [Ta25], only finitely many degrees $n \ge 3$ remain open.

Tags: polynomials, analysis.

## References

* [EHP58] Erdős, P., Herzog, F. and Piranian, G., _Metric properties of polynomials_. J.
  Analyse Math. (1958), 125–148.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Ha74] Hayman, W. K., _Research problems in function theory: new problems_ (1974), 155–180.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982),
  59–79.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999.
* [Do61] Dolzhenko, E. P., _Some estimates concerning algebraic hypersurfaces and derivatives
  of rational functions_. Dokl. Akad. Nauk SSSR (1961), 1287–1290.
* [Po59] Pommerenke, Ch., _On some problems by Erdős, Herzog and Piranian_. Michigan Math. J.
  (1959), 221–225.
* [Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J.
  (1961), 97–115.
* [Bo95] Borwein, P., _The arc length of the lemniscate $\{|p(z)|=1\}$_. Proc. Amer. Math. Soc.
  (1995), 797–799.
* [ErHa99] Eremenko, A. and Hayman, W., _On the length of lemniscates_. Michigan Math. J.
  (1999), 409–415.
* [Da07] Danchenko, V. I., _The lengths of lemniscates. Variations of rational functions_.
  Mat. Sb. (2007), 51–58.
* [FrNa09] Fryntov, A. and Nazarov, F., _New estimates for the length of the
  Erdős–Herzog–Piranian lemniscate_ (2009), 49–60.
* [Ta25] Tao, T., _The maximal length of the Erdős–Herzog–Piranian lemniscate in high
  degree_. arXiv:2512.12455 (2025).

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/114` for [EHP58],
[Ha74], [Va99], [Do61], [Po59], [Po61], [Bo95], [ErHa99], [Da07], [FrNa09] and [Ta25]. That
extraction gives the [Ta25] title as "… lemniscate length in high degree". The title above drops
the second "length", which looks like a typo; it was not checked against arXiv. Sibling
`/latex` extractions for [Er61], [Er82e], [Er90] and [Er97f]; they agree on [Va99]. No
extraction gives a venue for [Er82e].)
-/

/-- The unit level curve of a complex polynomial p: the set of z ∈ ℂ with |p(z)| = 1. -/
def levelCurveUnit (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ = 1}

/-- The arc length of a subset of ℂ, given by the 1-dimensional Hausdorff measure. -/
noncomputable def arcLength (S : Set ℂ) : ℝ≥0∞ :=
  Measure.hausdorffMeasure 1 S

/--
Erdős-Herzog-Piranian Conjecture (Problem #114) [EHP58]:
If p(z) ∈ ℂ[z] is a monic polynomial of degree n ≥ 1, then the length of the
curve {z ∈ ℂ : |p(z)| = 1} is maximized when p(z) = z^n - 1.

That is, for every monic polynomial p of degree n,
  length({z : |p(z)| = 1}) ≤ length({z : |z^n - 1| = 1}).

Known partial results (with f(n) the maximal length):
- The curve for p(z) = z^n - 1 has length 2n + O(1), so the conjecture implies
  the maximal length f(n) satisfies f(n) = 2n + O(1).
- Dolzhenko (1961) [Do61]: f(n) ≤ 4πn. Pommerenke (1961) [Po61]: f(n) ≪ n².
- Borwein (1995) [Bo95]: f(n) ≪ n.
- Eremenko–Hayman (1999) [ErHa99]: f(n) ≤ 9.173n; full conjecture holds for n = 2.
- Danchenko (2007) [Da07]: f(n) ≤ 2πn.
- Fryntov–Nazarov (2009) [FrNa09]: f(n) ≤ 2n + O(n^{7/8}); z^n - 1 is a local maximiser.
- Tao (2025) [Ta25]: z^n - 1 is the unique maximiser, up to rotation and translation, for all
  large n.
-/
theorem erdos_problem_114 :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) :=
  sorry

/--
Tao [Ta25] (PROVED): for all sufficiently large n, z^n - 1 is a maximiser, and it is unique up
to rotation and translation. Among monic polynomials of degree n, those are exactly
(z - c)^n - ω with |ω| = 1.
-/
theorem erdos_problem_114.variants.large_n :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤
        arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) ∧
      (arcLength (levelCurveUnit p) =
          arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ n - 1)) →
        ∃ c ω : ℂ, ‖ω‖ = 1 ∧ p = (X - C c) ^ n - C ω) :=
  sorry

/--
Eremenko and Hayman [ErHa99] (PROVED): the conjecture holds for n = 2.
-/
theorem erdos_problem_114.variants.deg_two :
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = 2 →
      arcLength (levelCurveUnit p) ≤
      arcLength (levelCurveUnit ((X : Polynomial ℂ) ^ 2 - 1)) :=
  sorry

/--
Danchenko [Da07] (PROVED): f(n) ≤ 2πn.
-/
theorem erdos_problem_114.variants.danchenko :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤ ENNReal.ofReal (2 * Real.pi * n) :=
  sorry

/--
Fryntov and Nazarov [FrNa09] (PROVED): f(n) ≤ 2n + O(n^{7/8}).
-/
theorem erdos_problem_114.variants.fryntov_nazarov :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤ ENNReal.ofReal (2 * n + C * (n : ℝ) ^ ((7 : ℝ) / 8)) :=
  sorry

/--
The question of [Va99] (PROVED, as a consequence of [Ta25] according to the page): f(n) ≤ 2n + O(1).
-/
theorem erdos_problem_114.variants.two_n_plus_const :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      arcLength (levelCurveUnit p) ≤ ENNReal.ofReal (2 * n + C) :=
  sorry

/--
Pommerenke [Po59] (PROVED), answering the companion question of [EHP58]: if {z : |p(z)| < 1} is
connected, the curve has length at least 2π. The example p(z) = z^n shows that 2π is best
possible.
-/
theorem erdos_problem_114.variants.pommerenke_connected :
    ∀ n : ℕ, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.Monic → p.natDegree = n →
      IsConnected {z : ℂ | ‖p.eval z‖ < 1} →
      ENNReal.ofReal (2 * Real.pi) ≤ arcLength (levelCurveUnit p) :=
  sorry
