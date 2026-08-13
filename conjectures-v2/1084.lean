import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Erdős Problem #1084

Let f_d(n) be minimal such that in any collection of n points in ℝ^d, all of
distance at least 1 apart, there are at most f_d(n) many pairs of points which
are distance 1 apart. Estimate f_d(n).

Equivalently, f_d(n) is the maximum number of unit-distance pairs among n
points in ℝ^d that are pairwise at distance at least 1 (a packing). This is
sometimes known as the contact number problem. Status: OPEN [Er75f, p.102].

Known results (erdosproblems.com/1084, page edition 08 February 2026):

- It is easy to see that f_1(n) = n - 1 and f_2(n) < 3n (at most 6 points can
  be at distance 1 from any point).
- Erdős [Er46b] showed f_2(n) < 3n - c·n^{1/2} for some constant c > 0, which
  the triangular lattice shows is best possible up to the value of c.
- In [Er75f] Erdős speculated the triangular lattice is exactly best possible,
  in particular f_2(3n² + 3n + 1) = 9n² + 3n. Harborth [Ha74b] proved this,
  and more generally f_2(n) = ⌊3n - √(12n - 3)⌋ for all n ≥ 2.
- In [Er75f] Erdős claims the existence of c₁, c₂ > 0 such that
  6n - c₁·n^{2/3} < f_3(n) < 6n - c₂·n^{2/3}. An upper bound
  f_3(n) < 6n - 0.926·n^{2/3} for all n ≥ 2 was proved by Bezdek and Reid
  [BeRe13]. (These d = 3 statements are recorded here but not formalized
  below: n^{2/3} needs the real-power import, which this file does not carry.)
- In general, it is known that (d - o(1))·n ≤ f_d(n) ≤ 2^{O(d)}·n, the lower
  bound coming from points arranged in an integer grid (o(1) as n → ∞ for
  each fixed d) and the upper bound from the fact that 2^{O(d)} many
  non-intersecting congruent balls can touch a fixed ball (the kissing number
  problem).
- A recent survey on contact numbers for sphere packings is by Bezdek and
  Khan [BeKh18].

See [223] for the analogous problem with maximal distance 1.

References (stubs; journal details beyond those recovered from the archived
site are deliberately left incomplete rather than guessed):

- [Er75f] Erdős, P., _On some problems of elementary and combinatorial
  geometry_. Annali di Matematica Pura ed Applicata (4) (1975), 99-108.
- [Er46b] Erdős, P., _On sets of distances of n points_. Amer. Math. Monthly
  (1946), 248-250.
- [Ha74b] Harborth, H. (1974).
- [BeRe13] Bezdek, K. and Reid, S. (2013).
- [BeKh18] Bezdek, K. and Khan, M. A., survey on contact numbers for sphere
  packings (2018).

Related OEIS sequences: A045945 (possible).

Tags: geometry | distances

The authoritative upstream formalization lives at
google-deepmind/formal-conjectures, FormalConjectures/ErdosProblems/1084.lean.
-/

open Finset

noncomputable section

/--
The number of unit-distance (contact) pairs among a finite point configuration.
-/
def unitDistPairs {d n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin d)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n =>
    p.1 < p.2 ∧ dist (pts p.1) (pts p.2) = 1)).card

/--
A packing: all distinct points are at distance at least 1 apart.
-/
def IsPacking {d n : ℕ} (pts : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i j : Fin n, i ≠ j → 1 ≤ dist (pts i) (pts j)

/--
The contact number f_d(n): the maximum number of unit-distance pairs among
n points in ℝ^d that form a packing (all pairwise distances ≥ 1).
-/
def contactNumber (d n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ pts : Fin n → EuclideanSpace ℝ (Fin d),
    IsPacking pts ∧ unitDistPairs pts = k }

/--
Erdős Problem #1084 [Er75f, p.102], dimension 1:

It is easy to see that f_1(n) = n - 1 (points at consecutive integers; on the
line only consecutive points of a 1-separated set can be at distance exactly 1).
-/
theorem erdos_problem_1084_dim1 (n : ℕ) (hn : 1 ≤ n) :
    contactNumber 1 n = n - 1 :=
  sorry

/--
Harborth [Ha74b] proved that for all n ≥ 2,
  f_2(n) = ⌊3n - √(12n - 3)⌋.
-/
theorem erdos_problem_1084_harborth (n : ℕ) (hn : 2 ≤ n) :
    contactNumber 2 n = ⌊(3 * (n : ℝ) - Real.sqrt (12 * n - 3))⌋₊ :=
  sorry

/--
The general lower bound (d - o(1))·n ≤ f_d(n), where the o(1) is as n → ∞
for each fixed dimension d; the construction is points arranged in an integer
grid [m]^d with m → ∞.

Note: an earlier version of this statement quantified the o(1) in d
(∀ ε > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n ≥ 1, (d - ε)·n ≤ f_d(n)), which is false:
for n = 1 there are no pairs, so f_d(1) = 0 < d - ε once d > ε. The bound
cannot hold uniformly in n for fixed d (a grid of side m has contact ratio
d(1 - 1/m), so n ≈ (d/ε)^d points are needed to reach d - ε).
-/
theorem erdos_problem_1084_general_lower (d : ℕ) :
    ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ((d : ℝ) - ε) * n ≤ (contactNumber d n : ℝ) :=
  sorry

/--
The general upper bound f_d(n) ≤ 2^{O(d)}·n, coming from the fact that at
most 2^{O(d)} non-intersecting congruent balls can touch a fixed ball (the
kissing number problem): in a packing each point has at most kissing-number
many neighbours at distance exactly 1.
-/
theorem erdos_problem_1084_general_upper :
    ∃ C > 0, ∀ d n : ℕ, 1 ≤ n →
      (contactNumber d n : ℝ) ≤ C ^ d * n :=
  sorry

/--
The easy planar upper bound f_2(n) < 3n: at most 6 points can be at distance
exactly 1 from any given point of a 1-separated planar set. (The hypothesis
1 ≤ n excludes the degenerate n = 0, where f_2(0) = 0 and 0 < 0 fails.)
-/
theorem erdos_problem_1084_easy_upper_dim2 (n : ℕ) (hn : 1 ≤ n) :
    contactNumber 2 n < 3 * n :=
  sorry

/--
Erdős [Er46b] showed f_2(n) < 3n - c·√n for some constant c > 0, which the
triangular lattice shows is best possible up to the value of c. (Any
0 < c < 3 works for all n ≥ 1, by Harborth's exact formula and
√(12n - 3) ≥ 3√n.)
-/
theorem erdos_problem_1084_er46b_dim2 :
    ∃ c > (0 : ℝ), ∀ n : ℕ, 1 ≤ n →
      (contactNumber 2 n : ℝ) < 3 * n - c * Real.sqrt n :=
  sorry

/--
In [Er75f] Erdős speculated that the triangular lattice is exactly best
possible in the plane, in particular f_2(3n² + 3n + 1) = 9n² + 3n; Harborth
[Ha74b] proved this. (Consistent with the closed formula: for
N = 3n² + 3n + 1 one has 12N - 3 = (6n + 3)², so
3N - √(12N - 3) = 9n² + 3n exactly; the n = 0 case reads f_2(1) = 0.)
-/
theorem erdos_problem_1084_triangular_dim2 (n : ℕ) :
    contactNumber 2 (3 * n ^ 2 + 3 * n + 1) = 9 * n ^ 2 + 3 * n :=
  sorry

end
