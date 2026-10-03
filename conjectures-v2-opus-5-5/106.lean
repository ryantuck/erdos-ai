-- [AI - Claude Opus 5.5]: Erdős Problem 106 — second-pass formalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open BigOperators Real

/-!
# Erdős Problem #106

*Source:* [erdosproblems.com/106](https://www.erdosproblems.com/106). Status at capture
(2026-02-19): **FALSIFIABLE** ("Open, but could be disproved with a finite
counterexample."). Current status: **DISPROVED (LEAN)**. The `teorth/erdosproblems` mirror
changed it from `falsifiable` to `disproved (Lean)` in the site owner's commit `7b7132c`
("Problem status updates", 2026-08-31). No upstream formal-conjectures file and no record of
the disproof itself are available in this container. [ErGr75b] [Er94b] [Er95]

Draw $n$ squares inside the unit square with no common interior point. Let $f(n)$ be the
maximum possible sum of the side-lengths of the squares. Is $f(k^2+1) = k$?

Remarks recorded on the page (capture of 2026-02-19, plus later fetches):
* In [Er94b] Erdős dates this conjecture to "more than 60 years ago". Erdős proved
  $f(2) = 1$ in an early paper for Hungarian high-school students. Newman proved, in a
  personal communication to Erdős, that $f(5) = 2$.
* It is trivial from the Cauchy–Schwarz inequality that $f(k^2) = k$. Erdős also asks for
  which $n$ it is true that $f(n+1) = f(n)$.
* $f(k^2+1) \ge k$: divide the unit square into $k^2$ squares of side $1/k$ and replace one
  by two squares of side $1/(2k)$.
* Halász [Ha84]: $f(k^2+2c+1) \ge k + \frac{c}{k}$ and $f(k^2+2c) \ge k + \frac{c}{k+1}$,
  stated for $c \ge 1$. Halász also considers parallelograms and triangles.
* Erdős and Soifer [ErSo95] and Campbell and Staton [CaSt05] conjectured
  $f(k^2+2c+1) = k + \frac{c}{k}$ for all integers $-k < c < k$, and proved the lower bound.
  Praton [Pr08] proved this general conjecture equivalent to $f(k^2+1) = k$.
* Baek, Koizumi and Ueoro [BKU24] proved $g(k^2+1) = k$, where $g$ is $f$ restricted to
  squares with sides parallel to the unit square. More generally they proved
  $g(k^2+2c+1) = k + c/k$ for $-k < c < k$, which determines all values of $g$.
* By March 2026 the page also cited Raj Singh [Ra26], with a statement about the series
  $\sum_{k \ge 1} (f(k^2+1) - k)$. Its exact content was not recovered.

**Polarity.** The question has been answered "no", so `erdos_problem_106` asserts the
negation of the first-pass statement: some $k \ge 1$ has $f(k^2+1) \ne k$. Since
$f(k^2+1) \ge k$, that means $f(k^2+1) > k$.

Tags: geometry.

## References

* [ErGr75b] Erdős, P. and Graham, R. L. (1975). Stub: not recovered.
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Ha84] Halász, S., _Packing a convex domain with similar convex domains_. J. Combin.
  Theory Ser. A (1984), 85–90.
* [ErSo95] Erdős, P. and Soifer, A., _Squares in a square_. Geombinatorics (1995), 110–114.
* [CaSt05] Campbell, C. and Staton, W., _A square-packing problem of Erdős_. Amer. Math.
  Monthly (2005), 165–167.
* [Pr08] Praton, I., _Packing squares in a square_. Math. Mag. (2008), 358–361.
* [BKU24] Baek, J., Koizumi, J. and Ueoro, T., _A note on the Erdős conjecture about square
  packing_. arXiv:2411.07274 (2024).
* [Ra26] Raj Singh, A., _On a square packing conjecture of Erdős_. arXiv:2601.22163 (2026).

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/106` (2026-03-15) for
everything except [ErGr75b], which is not in any extraction. That fetch's [Ha84] entry gives
the first name "Sylvia"; only the initial is used here. [Er95] comes from sibling
extractions.)
-/

/--
A square placement in ℝ²: a center point, a positive side length, and a
rotation angle (in radians) measuring how far the square is rotated from
the standard axis-aligned orientation.
-/
structure SquarePlacement where
  center : ℝ × ℝ
  side   : ℝ
  angle  : ℝ
  side_pos : 0 < side

/--
The closed region occupied by a square placement.  A point p lies in the
region iff, when translated so the center is at the origin and then rotated
by `-angle`, its coordinates both lie in `[-side/2, side/2]`.
-/
noncomputable def SquarePlacement.region (sq : SquarePlacement) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    let u :=  (p.1 - sq.center.1) * cos sq.angle + (p.2 - sq.center.2) * sin sq.angle
    let v := -(p.1 - sq.center.1) * sin sq.angle + (p.2 - sq.center.2) * cos sq.angle
    |u| ≤ sq.side / 2 ∧ |v| ≤ sq.side / 2}

/--
The open interior of a square placement (strict inequalities).
-/
noncomputable def SquarePlacement.sqInterior (sq : SquarePlacement) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ |
    let u :=  (p.1 - sq.center.1) * cos sq.angle + (p.2 - sq.center.2) * sin sq.angle
    let v := -(p.1 - sq.center.1) * sin sq.angle + (p.2 - sq.center.2) * cos sq.angle
    |u| < sq.side / 2 ∧ |v| < sq.side / 2}

/--
The unit square [0,1]² ⊆ ℝ².
-/
def unitSquare : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/--
A valid configuration of `n` squares inside the unit square:
1. Each square's closed region is contained in the unit square.
2. No two distinct squares share an interior point (their open interiors
   are disjoint).
-/
def IsValidSquareConfig (n : ℕ) (config : Fin n → SquarePlacement) : Prop :=
  (∀ i : Fin n, (config i).region ⊆ unitSquare) ∧
  (∀ i j : Fin n, i ≠ j → Disjoint (config i).sqInterior (config j).sqInterior)

/--
`f n` is the supremum of the total side-length sum over all valid configurations
of `n` (possibly rotated) squares inside the unit square with pairwise disjoint
interiors.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ config : Fin n → SquarePlacement,
    IsValidSquareConfig n config ∧ s = ∑ i : Fin n, (config i).side}

/--
Erdős Problem #106 (DISPROVED, per the `teorth/erdosproblems` mirror, 2026-08-31):

Draw `n` squares (not necessarily axis-aligned) inside the unit square [0,1]²
with no two squares sharing a common interior point.  Let `f(n)` be the maximum
possible sum of the side-lengths of the squares. Is `f(k² + 1) = k` for every positive
integer `k`? **No.** The statement under `¬` is the first-pass statement, byte for byte.

Background:
- It follows easily from the Cauchy–Schwarz inequality that `f(k²) = k`.
- The lower bound `f(k² + 1) ≥ k` is elementary: subdivide [0,1]² into k²
  squares of side 1/k, then replace any one of them by two squares of side
  1/(2k); the total side-length is (k² − 1)/k + 2·(1/(2k)) = k.
- Baek, Koizumi, and Ueoro [BKU24] proved the axis-aligned variant: if all
  squares are required to have sides parallel to the coordinate axes, then the
  supremum equals k.
-/
theorem erdos_problem_106 :
    ¬ (∀ k : ℕ, 0 < k → f (k ^ 2 + 1) = (k : ℝ)) :=
  sorry

/--
Cauchy–Schwarz (PROVED, trivial): $f(k^2) = k$ for $k \ge 1$.
-/
theorem erdos_problem_106.variants.square_count (k : ℕ) (hk : 0 < k) :
    f (k ^ 2) = (k : ℝ) :=
  sorry

/--
The elementary lower bound (PROVED): $f(k^2+1) \ge k$.
-/
theorem erdos_problem_106.variants.lower_bound (k : ℕ) (hk : 0 < k) :
    (k : ℝ) ≤ f (k ^ 2 + 1) :=
  sorry

/--
Erdős and Newman (PROVED): $f(2) = 1$ and $f(5) = 2$. These are the cases $k = 1, 2$ of the
first-pass conjecture, so any counterexample has $k \ge 3$.
-/
theorem erdos_problem_106.variants.small_cases : f 2 = 1 ∧ f 5 = 2 :=
  sorry

/--
Halász [Ha84] (PROVED): $f(k^2+2c+1) \ge k + \frac{c}{k}$ and $f(k^2+2c) \ge k + \frac{c}{k+1}$.
Here they are stated for $1 \le c \le k$. The page says "for any $c \ge 1$", but the first
bound contradicts Cauchy–Schwarz ($f(n) \le \sqrt n$) as soon as $c > k$: at $(k, c) = (1, 2)$
it would give $f(6) \ge 3 > \sqrt6$. The second fails for $c \ge 2k+3$.
-/
theorem erdos_problem_106.variants.halasz (k c : ℕ) (hk : 0 < k) (hc : 1 ≤ c) (hck : c ≤ k) :
    (k : ℝ) + c / k ≤ f (k ^ 2 + 2 * c + 1) ∧ (k : ℝ) + c / (k + 1) ≤ f (k ^ 2 + 2 * c) :=
  sorry

/--
The Erdős–Soifer / Campbell–Staton general conjecture fails too (a consequence of
`erdos_problem_106`): its case $c = 0$ is $f(k^2+1) = k$. The argument of `f` is
$k^2 + 2c + 1 > 0$ because $c > -k$.
-/
theorem erdos_problem_106.variants.general_conjecture_false :
    ¬ (∀ k : ℕ, 0 < k → ∀ c : ℤ, -(k : ℤ) < c → c < k →
      f ((k : ℤ) ^ 2 + 2 * c + 1).toNat = (k : ℝ) + (c : ℝ) / k) :=
  sorry

/--
`fAxis n`: the same supremum, restricted to axis-parallel squares (rotation angle `0`). This is
the function $g$ of [BKU24].
-/
noncomputable def fAxis (n : ℕ) : ℝ :=
  sSup {s : ℝ | ∃ config : Fin n → SquarePlacement,
    IsValidSquareConfig n config ∧ (∀ i, (config i).angle = 0) ∧
      s = ∑ i : Fin n, (config i).side}

/--
Baek, Koizumi and Ueoro [BKU24] (PROVED): for axis-parallel squares,
$g(k^2+2c+1) = k + c/k$ for all $-k < c < k$. The case $c = 0$ is $g(k^2+1) = k$.
-/
theorem erdos_problem_106.variants.axis_parallel :
    ∀ k : ℕ, 0 < k → ∀ c : ℤ, -(k : ℤ) < c → c < k →
      fAxis ((k : ℤ) ^ 2 + 2 * c + 1).toNat = (k : ℝ) + (c : ℝ) / k :=
  sorry
