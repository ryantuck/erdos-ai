-- [AI - Claude Opus 5.5]: Erdős Problem 107 — second-pass formalization
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

open Set

/-!
# Erdős Problem #107

*Source:* [erdosproblems.com/107](https://www.erdosproblems.com/107) (status **FALSIFIABLE**,
\$500: "Open, but could be disproved with a finite counterexample."; page last edited
23 January 2026, captured 2026-02-19 and 2026-03-05). [Er61, p.245] [Er75f, p.106] [Er81]
[Er82e] [Er83c] [Er95, p.184] [Er97c] [Er97e] [Va99, 4.66]

Let $f(n)$ be minimal such that any $f(n)$ points in $\mathbb{R}^2$, no three on a line,
contain $n$ points which form the vertices of a convex $n$-gon. Prove that
$f(n) = 2^{n-2} + 1$.

Remarks recorded on the page:
* The Erdős–Klein–Szekeres "Happy Ending" problem. It originated in 1931 when Klein observed
  that $f(4) = 5$. Turán and Makai showed $f(5) = 9$.
* Erdős and Szekeres proved $2^{n-2} + 1 \le f(n) \le \binom{2n-4}{n-2} + 1$ ([ErSz60] and
  [ErSz35] respectively).
* Several improvements of the upper bound were all of the form $4^{(1+o(1))n}$, until Suk
  [Su17] proved $f(n) \le 2^{(1+o(1))n}$. The current best bound is due to Holmsen, Mojarrad,
  Pach and Tardos [HMPT20]: $f(n) \le 2^{n + O(\sqrt{n \log n})}$.
* In [Er97e] Erdős clarifies that the \$500 is for a proof; he offers only \$100 for a
  disproof. This is #1 in Ramsey Theory in the graphs problem collection.
* See also Problems #216, #651 and #838.

**Encoding.** The plane is `Fin 2 → ℝ`. Its sup metric is irrelevant here, because
collinearity, convex hulls and extreme points are affine notions. $f(n) = 2^{n-2}+1$ is
encoded as two halves:
* every general-position set of at least $2^{n-2}+1$ points contains a convex $n$-gon. This
  is the open half.
* some general-position set of exactly $2^{n-2}$ points does not. This is [ErSz60], proved.
Supersets and subsets of general-position sets are again in general position, so the two
halves are equivalent to $f(n) = 2^{n-2}+1$.

Tags: geometry, convex. OEIS: A000051.

## References

* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl.
  (1961), 221–254.
* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_. (1982),
  59–79.
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999.
* [ErSz35] Erdős, P. and Szekeres, G., _A combinatorial problem in geometry_. Compos. Math.
  (1935), 463–470.
* [ErSz60] Erdős, P. and Szekeres, G., _On some extremum problems in elementary geometry_.
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (1960/61), 53–62.
* [Su17] Suk, A., _On the Erdős–Szekeres convex polygon problem_. J. Amer. Math. Soc. (2017),
  1047–1053.
* [HMPT20] Holmsen, A. F., Mojarrad, H. N., Pach, J. and Tardos, G., _Two extensions of the
  Erdős–Szekeres problem_. J. Eur. Math. Soc. (JEMS) (2020), 3981–3995.

(Provenance: the Erdős keys and [Va99] come from the original pipeline's `/latex` extractions
for sibling problems. [ErSz60]'s title also appears in a `/latex` extraction. The full
entries for [ErSz35], [ErSz60], [Su17] and [HMPT20] come from upstream formal-conjectures
`ErdosProblems/107.lean` at `df3f12d`.)
-/

/-- Points in ℝ² are in **general position** if no three are collinear. -/
def GeneralPosition (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬Collinear ℝ ({p₁, p₂, p₃} : Set (Fin 2 → ℝ))

/-- A finite set of points in ℝ² is in **convex position** if every point
is an extreme point of the convex hull of the set. -/
def ConvexPosition (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ p ∈ S, p ∈ (convexHull ℝ (↑S : Set (Fin 2 → ℝ))).extremePoints ℝ

/--
Erdős Problem #107 [Er61, Er75f, Er81, Er82e, Er83c, Er95, Er97c, Er97e, Va99]
(FALSIFIABLE, \$500 for a proof):

The Erdős-Klein-Szekeres 'Happy Ending' problem. Let f(n) be minimal such that
any f(n) points in ℝ², no three on a line, contain n points which form the
vertices of a convex n-gon. Prove that f(n) = 2^{n-2} + 1.

The lower bound f(n) ≥ 2^{n-2} + 1, i.e. the second conjunct, was proved by Erdős and
Szekeres [ErSz60]. The upper bound f(n) ≤ C(2n-4, n-2) + 1 was proved in [ErSz35], with the
best current bound f(n) ≤ 2^{n+O(√(n log n))} due to Holmsen, Mojarrad, Pach, and
Tardos [HMPT20].
-/
theorem erdos_problem_107 (n : ℕ) (hn : n ≥ 3) :
    (∀ (S : Finset (Fin 2 → ℝ)),
      S.card ≥ 2 ^ (n - 2) + 1 →
      GeneralPosition S →
      ∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T) ∧
    (∃ (S : Finset (Fin 2 → ℝ)),
      S.card = 2 ^ (n - 2) ∧
      GeneralPosition S ∧
      ¬∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T) :=
  sorry

/-- `S` contains `n` points in convex position, i.e. the vertices of a convex `n`-gon. -/
def HasConvexSubset (n : ℕ) (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T

/--
Klein (PROVED): $f(4) = 5$.
-/
theorem erdos_problem_107.variants.klein :
    (∀ S : Finset (Fin 2 → ℝ), S.card ≥ 5 → GeneralPosition S → HasConvexSubset 4 S) ∧
    (∃ S : Finset (Fin 2 → ℝ), S.card = 4 ∧ GeneralPosition S ∧ ¬ HasConvexSubset 4 S) :=
  sorry

/--
Turán and Makai (PROVED): $f(5) = 9$.
-/
theorem erdos_problem_107.variants.turan_makai :
    (∀ S : Finset (Fin 2 → ℝ), S.card ≥ 9 → GeneralPosition S → HasConvexSubset 5 S) ∧
    (∃ S : Finset (Fin 2 → ℝ), S.card = 8 ∧ GeneralPosition S ∧ ¬ HasConvexSubset 5 S) :=
  sorry

/--
Erdős–Szekeres lower bound [ErSz60] (PROVED): $f(n) \ge 2^{n-2} + 1$. This is the second
conjunct of `erdos_problem_107`, stated on its own.
-/
theorem erdos_problem_107.variants.erdos_szekeres_lower (n : ℕ) (hn : n ≥ 3) :
    ∃ S : Finset (Fin 2 → ℝ),
      S.card = 2 ^ (n - 2) ∧ GeneralPosition S ∧ ¬ HasConvexSubset n S :=
  sorry

/--
Erdős–Szekeres upper bound [ErSz35] (PROVED): $f(n) \le \binom{2n-4}{n-2} + 1$.
-/
theorem erdos_problem_107.variants.erdos_szekeres_upper (n : ℕ) (hn : n ≥ 3) :
    ∀ S : Finset (Fin 2 → ℝ),
      S.card ≥ (2 * n - 4).choose (n - 2) + 1 → GeneralPosition S → HasConvexSubset n S :=
  sorry

/--
Holmsen, Mojarrad, Pach and Tardos [HMPT20] (PROVED): $f(n) \le 2^{n + O(\sqrt{n \log n})}$.
This improves Suk's $2^{(1+o(1))n}$ [Su17].
-/
theorem erdos_problem_107.variants.hmpt :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      ∀ S : Finset (Fin 2 → ℝ),
        (2 : ℝ) ^ ((n : ℝ) + C * Real.sqrt (n * Real.log n)) ≤ (S.card : ℝ) →
        GeneralPosition S → HasConvexSubset n S :=
  sorry
