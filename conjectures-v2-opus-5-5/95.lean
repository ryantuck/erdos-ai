-- [AI - Claude Opus 5.5]: Erdős Problem 95 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #95

*Source:* [erdosproblems.com/95](https://www.erdosproblems.com/95). Status at capture
(2026-02-22): **PROVED**, \$500 ("This has been solved in the affirmative."). The
`teorth/erdosproblems` mirror now records `proved (Lean)` (formal status updated
2026-08-24). [Er92e] [Er95] [Er97c] [Er97f]

Let $x_1, \ldots, x_n \in \mathbb{R}^2$ determine the set of distances
$\{u_1, \ldots, u_t\}$. Suppose $u_i$ appears as the distance between $f(u_i)$ many pairs
of points. Then for all $\varepsilon > 0$, $\sum_i f(u_i)^2 \ll_\varepsilon n^{3+\varepsilon}$.

Remarks recorded on the page:
* "The case when the points determine a convex polygon was solved by Fishburn [Al63]." The
  key [Al63] is Altman's paper (see below). The convex case of this bound is Problem #94,
  where Erdős credits Fishburn without a reference and Lefmann and Thiele gave a proof.
* It is trivial that $\sum_i f(u_i) = \binom{n}{2}$.
* Solved by Guth and Katz [GuKa15], who proved $\sum_i f(u_i)^2 \ll n^3 \log n$.
* See also Problem #94.

**Encoding.** `distMultiplicity95 P d` counts *ordered* pairs, which is $2 f(d)$. The sum
of its squares is therefore $4 \sum_i f(u_i)^2$, and the factor 4 is absorbed by the
constant `C`.

Tags: geometry, convex, distances. OEIS: "possible".

## References

* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Al63] Altman, E., _On a problem of P. Erdős_. Amer. Math. Monthly (1963), 148–157.
* [GuKa15] Guth, L. and Katz, N. H., _On the Erdős distinct distances problem in the plane_.
  Ann. of Math. (2) (2015), 155–190.

(Provenance: [GuKa15] from the original pipeline's fetch of `erdosproblems.com/latex/95`.
[Er92e] and [Er97c] from `/latex/94`, [Al63] from `/latex/93`, [Er95] from `/latex/75`, and
[Er97f] from sibling extractions. All agree with upstream formal-conjectures at `df3f12d`.)
-/

/--
The set of distinct distances determined by a finite point set P in ℝ².
-/
noncomputable def distinctDistances95 (P : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((P.product P).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2)

/--
The number of ordered pairs (p, q) from P with p ≠ q and dist(p, q) = d.
-/
noncomputable def distMultiplicity95 (P : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((P.product P).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = d)).card

/--
Erdős Problem #95 (PROVED):
Let x₁, ..., xₙ ∈ ℝ² determine the set of distances {u₁, ..., uₜ}. Suppose uᵢ
appears as the distance between f(uᵢ) many pairs of points. Then for all ε > 0,
  ∑ᵢ f(uᵢ)² ≪_ε n^{3+ε}.

This was proved by Guth and Katz [GuKa15], who showed the stronger bound
  ∑ᵢ f(uᵢ)² ≪ n³ log n.
-/
theorem erdos_problem_95 :
    ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧
        ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
          ((distinctDistances95 P).sum
            (fun d => (distMultiplicity95 P d) ^ 2) : ℝ) ≤
            C * (P.card : ℝ) ^ ((3 : ℝ) + ε) :=
  sorry

/--
Guth and Katz [GuKa15] (PROVED): $\sum_i f(u_i)^2 \ll n^3 \log n$. No size guard is needed:
for $|P| \le 1$ the left side is $0$, and so is the right side, since `Real.log 0 = 0` and
`Real.log 1 = 0`.
-/
theorem erdos_problem_95.variants.guth_katz :
    ∃ C : ℝ, C > 0 ∧
      ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
        ((distinctDistances95 P).sum
          (fun d => (distMultiplicity95 P d) ^ 2) : ℝ) ≤
          C * (P.card : ℝ) ^ 3 * Real.log (P.card : ℝ) :=
  sorry

/--
The trivial identity $\sum_i f(u_i) = \binom{n}{2}$, stated for ordered pairs: the
multiplicities sum to $n(n-1)$. This pins down that `distMultiplicity95` counts ordered
pairs.
-/
theorem erdos_problem_95.variants.sum_multiplicity (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    (distinctDistances95 P).sum (fun d => distMultiplicity95 P d) = P.card * (P.card - 1) :=
  sorry
