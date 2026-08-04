import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/--
The number of unit-distance pairs in a finite point set in ℝᵈ:
the number of unordered pairs {p, q} with p ≠ q and dist(p, q) = 1.
-/
def unitDistancePairsD (d : ℕ) (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((A.product A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card / 2

/--
f_d(n): the maximum number of unit-distance pairs among all sets of n points in ℝᵈ.

The set of achievable counts is nonempty for d ≥ 1 (the space is infinite, so
n-point sets exist) and bounded above by n², so `sSup` is a genuine maximum there.
Degenerate case: for d = 0 the space is a single point, so for n ≥ 2 the set is
empty and `sSup ∅ = 0` (junk value); the theorems below only use d ≥ 4.
-/
def maxUnitDistancePairs (d n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin d)), A.card = n ∧ unitDistancePairsD d A = k}

/--
Erdős Problem #1085 [Er75f,p.103]:

Verbatim from erdosproblems.com/1085 (page edition 17 October 2025, status OPEN):
"Let $f_d(n)$ be minimal such that, in any set of $n$ points in $\mathbb{R}^d$,
there exist at most $f_d(n)$ pairs of points which distance $1$ apart.
Estimate $f_d(n)$."

Equivalently, f_d(n) is the maximum number of pairs of points at distance 1 in
any set of n points in ℝᵈ (`maxUnitDistancePairs` above).

The most difficult cases are d = 2 and d = 3, which remain open. When d = 2 this
is the unit distance problem (Erdős Problem #90, formalized separately in this
repo as `erdos_problem_90`), with best known bounds
n^{1+c/log log n} < f_2(n) ≪ n^{4/3} (lower: Erdős [Er46b]; upper: Spencer,
Szemerédi, and Trotter [SST84]). When d = 3 the best known bounds are
n^{4/3} log log n ≪ f_3(n) ≪ n^{3/2} β(n) for a very slowly growing β (lower:
Erdős [Er60b]; upper: Clarkson, Edelsbrunner, Guibas, Sharir, and Welzl
[CEGSW90]).

For d ≥ 4 with p = ⌊d/2⌋, the answer is known to be asymptotically
((p-1)/(2p)) · n². Specifically:

Lower bound (Lenz construction): f_d(n) ≥ ((p-1)/(2p)) · n² - O(1).
Upper bound (Erdős [Er60b], via Erdős–Stone): f_d(n) ≤ ((p-1)/(2p) + o(1)) · n².

Moreover Erdős [Er67e] determined f_d(n) up to O(1) for all even d ≥ 4, Brass
[Br97] determined f_4(n) exactly, Swanepoel [Sw09] determined f_d(n) exactly for
even d ≥ 6, and for odd d ≥ 5 Erdős and Pach [ErPa90] proved
(p-1)/(2p) n² + c₁ n^{4/3} ≤ f_d(n) ≤ (p-1)/(2p) n² + c₂ n^{4/3} for constants
c₁(d), c₂(d) > 0. (These exact/refined results are not formalized here: the
exact formulas are not stated on the page, and n^{4/3} would need `Real.rpow`,
which this file does not use.)

We formalize the solved d ≥ 4 upper bound: for every ε > 0, for all sufficiently
large finite sets A ⊆ ℝᵈ with d ≥ 4, the number of unit-distance pairs is at
most ((p-1)/(2p) + ε) · |A|². An upstream formalization also exists at
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1085.lean).

References:
[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Ann. Mat. Pura Appl. (4) (1975), 99-108.
[Er46b] Erdős, P., _On sets of distances of n points_. Amer. Math. Monthly
(1946), 248-250.
[SST84] Spencer, J., Szemerédi, E., and Trotter, W. T., 1984. (Details not
recoverable offline.)
[Er60b] Erdős, P., _On sets of distances of n points in Euclidean space_.
Magyar Tudományos Akadémia Matematikai Kutatóintézet Közleményei (1960),
165-169.
[CEGSW90] Clarkson, K. L., Edelsbrunner, H., Guibas, L. J., Sharir, M.,
Welzl, E., _Combinatorial complexity bounds for arrangements of curves and
spheres_. Discrete Comput. Geom. (1990), 99-160.
[Er67e] Erdős, P., 1967. (Details not recoverable offline.)
[Br97] Brass, P., 1997. (Details not recoverable offline.)
[Sw09] Swanepoel, K. J., _Unit distances and diameters in Euclidean spaces_.
Discrete & Computational Geometry (2009), 1-27.
[ErPa90] Erdős, P. and Pach, J., _Variations on the theme of repeated
distances_. Combinatorica (1990), 261-269.
-/
theorem erdos_problem_1085 (d : ℕ) (hd : 4 ≤ d) :
    let p := d / 2
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin d))),
        N₀ ≤ A.card →
        (unitDistancePairsD d A : ℝ) ≤
          ((↑p - 1) / (2 * ↑p) + ε) * (A.card : ℝ) ^ 2 :=
  sorry

/--
Lenz's construction (points distributed over p = ⌊d/2⌋ pairwise-orthogonal
circles of radius 1/√2): for d ≥ 4, f_d(n) ≥ ((p-1)/(2p)) · n² - O(1)
[erdosproblems.com/1085, solved].

The page states the bound with an O(1) error term; since a balanced split of n
points over the p circles already yields at least ((p-1)/(2p)) n² - p/8 cross
pairs, a single constant C works for all n simultaneously (small n are absorbed
by enlarging C), so the ∃ C ∀ n form below is equivalent to the eventual form.
-/
theorem erdos_problem_1085.variants.lenz_lower (d : ℕ) (hd : 4 ≤ d) :
    let p := d / 2
    ∃ C : ℝ, ∀ n : ℕ,
      ((↑p - 1) / (2 * ↑p)) * (n : ℝ) ^ 2 - C ≤ (maxUnitDistancePairs d n : ℝ) :=
  sorry

end
