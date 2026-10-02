-- [AI - Claude Opus 5.5]: Erdős Problem 92 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset Filter Topology

noncomputable section

/-!
# Erdős Problem #92

*Source:* [erdosproblems.com/92](https://www.erdosproblems.com/92). Status at capture
(2026-03-05; page last edited 28 December 2025): **OPEN**, \$500 ("This is open, and cannot
be resolved with a finite computation."). Current status: **DISPROVED**. The
`teorth/erdosproblems` mirror records `disproved` (last update 2026-05-21), and upstream
formal-conjectures records both questions as `answer(False)`, quoting the page: "This is a
stronger form of the unit distance conjecture (see [90]). As such the recent disproof of
[90] also disproves this." [Er75f, p.100] [Er94b] [Er95, p.180] [Er97c, p.65]

Let $f(n)$ be maximal such that there exists a set $A$ of $n$ points in $\mathbb{R}^2$ in
which every $x \in A$ has at least $f(n)$ points in $A$ equidistant from $x$.

Is it true that $f(n) \le n^{o(1)}$? Or even $f(n) < n^{O(1/\log\log n)}$?

Remarks recorded on the page:
* The set of lattice points implies $f(n) > n^{c/\log\log n}$ for some constant $c > 0$.
  Erdős offered \$500 for a proof that $f(n) \le n^{o(1)}$ but only \$100 for a
  counterexample; the latter prize is downgraded to \$50 in [ErFi97].
* It is trivial that $f(n) \ll n^{1/2}$. A result of Pach and Sharir (Theorem 4 of
  [PaSh92]) implies $f(n) \ll n^{2/5}$. Hunter observed that the circle–point incidence
  bound of Janzer, Janzer, Methuku and Tardos [JJMT24] implies $f(n) \ll n^{4/11}$.
* Fishburn (personal communication to Erdős, later published in [ErFi97]) proved that 6 is
  the smallest $n$ with $f(n) = 3$ and 8 is the smallest $n$ with $f(n) = 4$, and suggested
  that the lattice points may not be the best example.
* See also Problem #754.

**Why the disproof of #90 disproves both questions.** The #90 disproof gives $c > 0$ and,
for infinitely many $n$, sets $P$ of $n$ points with at least $n^{1+c}$ unit distances.
Delete points of unit-degree $< n^c$ one at a time. Each deletion removes fewer than $n^c$
unit pairs, so a nonempty set $A \subseteq P$ survives in which every point has at least
$n^c \ge |A|^c$ points of $A$ at distance $1$. Since $|A| > n^c$, this gives
$f(m) \ge m^c$ for infinitely many $m$. That contradicts $f(n) \le n^{o(1)}$, and a
fortiori $f(n) < n^{O(1/\log\log n)}$.

Tags: geometry, distances. OEIS: "possible".

## References

* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
  Pura Appl. (4) (1975), 99–108.
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.
* [ErFi97] Erdős, P. and Fishburn, P. (1997). Stub: title and venue not recovered.
* [PaSh92] Pach, J. and Sharir, M., _Repeated angles in the plane and related problems_.
  J. Combin. Theory Ser. A (1992), 12–22.
* [JJMT24] Janzer, Janzer, Methuku and Tardos (2024). Stub: title and venue not recovered.
* Disproof of #90, as recorded upstream: W. Sawin, _An explicit lower bound for the unit
  distance problem_, arXiv:2605.20579 (2026); N. Alon, T. F. Bloom, W. T. Gowers, D. Litt,
  W. Sawin, A. Shankar, J. Tsimerman, V. Wang and M. Matchett Wood, _Remarks on the disproof
  of the unit distance conjecture_, arXiv:2605.20695 (2026).

(Provenance: the original pipeline's fetches of `erdosproblems.com/latex/N`: N = 1088/1090
for [Er75f], 106/755 for [Er94b], 75/843 for [Er95], 94 for [Er97c] and 1086 for [PaSh92].
The 2026 arXiv entries come from upstream `FormalConjectures/ErdosProblems/90.lean` at
`df3f12d`.)
-/

/--
For a point `x` and a finite set `A` in ℝ², the maximum number of other points
in `A` that are all at the same distance from `x`.
-/
def maxEquidistantCount (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  A.sup (fun y => (A.filter (fun z => z ≠ x ∧ dist x z = dist x y)).card)

/--
Every point `x ∈ A` has at least `k` other points of `A` lying on one circle centred at `x`.
-/
def HasEquidistantProperty (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ x ∈ A, k ≤ maxEquidistantCount A x

/--
The function $f(n)$ of the problem: the largest `k` such that some `n`-point set in ℝ² has
`HasEquidistantProperty k`.

For `n ≥ 1` the set of such `k` is nonempty (it contains `0`) and bounded by `n - 1`, so
`sSup` is its maximum. For `n = 0` the property holds vacuously for every `k`, the set is
unbounded, and `sSup` returns the junk value `0`. That is irrelevant to the asymptotic
statements below.
-/
def equidistantF (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧ HasEquidistantProperty k A}

/--
Erdős Problem #92 (DISPROVED, via the disproof of #90): it is **not** true that
$f(n) \le n^{o(1)}$. This is the \$500 question, stated in its true (negated) direction.

The first-pass statement bounded `maxEquidistantCount A x` for **every** `x ∈ A` by
`|A| ^ (C / log log |A|)`. That is false for reasons unrelated to the problem:
* a point together with `n - 1` points on a circle around it has count `n - 1` at the centre;
* at `|A| = 2` the exponent `C / log (log 2)` is negative, so the bound is `< 1`, while the
  count is `1`.

The problem's $f(n)$ is a max–min quantity, encoded here by `equidistantF`.
-/
theorem erdos_problem_92 :
    ¬ ∃ o : ℕ → ℝ, Tendsto o atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, (equidistantF n : ℝ) ≤ (n : ℝ) ^ o n :=
  sorry

/--
The stronger form, also DISPROVED: it is not true that $f(n) < n^{C/\log\log n}$ for some
$C > 0$ and all large $n$. This follows from `erdos_problem_92`, because
$C/\log\log n \to 0$.
-/
theorem erdos_problem_92.variants.strong :
    ¬ ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, (equidistantF n : ℝ) < (n : ℝ) ^ (C / Real.log (Real.log n)) :=
  sorry

/--
The explicit form of the disproof (see the module docstring): there is $c > 0$ with
$f(n) \ge n^c$ for infinitely many $n$. It is equivalent to `erdos_problem_92`.
-/
theorem erdos_problem_92.variants.polynomial_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ n : ℕ in atTop, (n : ℝ) ^ c ≤ (equidistantF n : ℝ) :=
  sorry

/--
Pach and Sharir (Theorem 4 of [PaSh92]): $f(n) \ll n^{2/5}$.
-/
theorem erdos_problem_92.variants.upper_bound_two_fifths :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (equidistantF n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / 5) :=
  sorry

/--
Hunter's observation, via the circle–point incidence bound of [JJMT24]:
$f(n) \ll n^{4/11}$.
-/
theorem erdos_problem_92.variants.upper_bound_four_elevenths :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (equidistantF n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 11) :=
  sorry

/--
Fishburn [ErFi97]: 6 is the smallest `n` with $f(n) = 3$, and 8 is the smallest `n` with
$f(n) = 4$.
-/
theorem erdos_problem_92.variants.fishburn :
    equidistantF 6 = 3 ∧ (∀ n < 6, equidistantF n ≠ 3) ∧
      equidistantF 8 = 4 ∧ (∀ n < 8, equidistantF n ≠ 4) :=
  sorry

end
