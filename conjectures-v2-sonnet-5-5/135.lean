-- [AI - Claude Sonnet 5.5]: Erdős Problem 135 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical Filter

/-!
# Erdős Problem #135: Few Distinct Distances Without Repeated Four-Point Patterns

*Source:* [erdosproblems.com/135](https://www.erdosproblems.com/135) (banner **DISPROVED**, prize
**\$250**: "This has been solved in the negative."; page last edited 16 January 2026; captured
2026-02-20 as the tidied problem box). [Er97b, p.231] [Er97e, p.531]

Let $A\subset \mathbb{R}^2$ be a set of $n$ points such that any subset of size $4$ determines at
least $5$ distinct distances. Must $A$ determine $\gg n^2$ many distances?

Remarks recorded on the page:
* A problem of Erdős and Gyárfás. Erdős could not even prove that the number of distances is at
  least $f(n)n$ where $f(n)\to \infty$. Erdős [Er97b] also makes the even stronger conjecture that
  $A$ must contain $\gg n$ many points such that all pairwise distances are distinct.
* Answered in the negative by Tao [Ta24c], who proved that for any large $n$ there exists a set of
  $n$ points in $\mathbb{R}^2$ such that any four points determine at least five distinct
  distances, yet there are $\ll n^2/\sqrt{\log n}$ distinct distances in total. Tao discusses his
  solution in a blog post.
* More generally, one can ask how many distances $A$ must determine if every set of $p$ points
  determines at least $q$ distances.
* See also [136], [657], and [659].

Tags: distances, geometry. OEIS: "Possible". 0 comments at capture.

**Status.** DISPROVED at capture. The mirror (`teorth/erdosproblems`) has `disproved` for the
informal status since 2025-08-31 and `disproved (Lean)` since 2026-08-24, which records a Lean
proof after the capture; it was not checked here. Upstream has no `135.lean` at the pinned
snapshot. The main theorem asserts the negation, the corpus convention for a refuted question.

**What the first pass got wrong, and what this file does.** The first pass asserted the refuted "yes"
direction, although its docstring records Tao's disproof. Wrapping its proposition in `¬ (…)` would
not repair it either. That proposition is false for a trivial reason: a single point has no
distances, so `c * 1 ≤ 0` fails for every `c > 0` (`variants.first_pass_false`). The negation would
then be provable without Tao's theorem. The page's "$\gg n^2$" is an asymptotic statement, so v2
adds the guard `N ≤ A.card`, and the main theorem is the negation of the guarded statement.

**Encoding.**
* `numDistances A` counts the distinct values of `dist p q` over ordered pairs of distinct points.
  An unordered pair gives the same value in both orders, so this is the number of distinct
  distances.
* `FourPointFiveDist A` says that every $4$-element subset has at least $5$ distinct distances. Four
  points have $6$ pairs, so at most one coincidence is allowed. It is vacuous for sets of at most
  $3$ points.
* "$A$ determines $\gg n^2$ distances" is `∃ c > 0, ∃ N, ∀ A, N ≤ |A| → FourPointFiveDist A →
  c |A|² ≤ numDistances A`. The guard is needed because the statement is false for $|A|=1$.
* Tao's bound is `variants.tao`: for some `C` and all large `n` there is a set of `n` points with the
  four-point property and at most `C n² / √(log n)` distinct distances. `variants.main_of_tao`
  proves the main theorem from it.
* The stronger conjecture of Erdős is `variants.stronger_conjecture_false`. It implies the first
  question, since $m$ points with all distances distinct determine $\binom m2$ distances, so the
  main theorem refutes it as well.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231. The page cites p. 231.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997), 527–537. The page
  cites p. 531.
* [Ta24c] Tao, T., _Planar point sets with forbidden 4-point patterns and few distinct distances_.
  arXiv:2409.01343 (2024). Blog post:
  `https://terrytao.wordpress.com/2024/09/03/planar-point-sets-with-forbidden-four-point-patterns-and-few-distinct-distances/`.

(Provenance: [Er97b] and [Ta24c] are from the `/latex/135` fetch in the session logs. [Er97e] is from
the bibliographies of the `/latex` pages of other problems.)
-/

/-- The number of distinct pairwise distances in a finite point set A ⊆ ℝ². -/
noncomputable def numDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)).card

/-- A finite point set A ⊆ ℝ² satisfies the "four-point, five-distance" property
    if every 4-element subset determines at least 5 distinct pairwise distances. -/
def FourPointFiveDist (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ A → S.card = 4 → 5 ≤ numDistances S

/--
Erdős–Gyárfás Conjecture (Problem #135) [Er97b, Er97e] — DISPROVED (prize $250):
Let A ⊆ ℝ² be a set of n points such that any 4 points determine at least 5
distinct distances. Must A determine ≫ n² many distances?

This was answered in the NEGATIVE by Tao [Ta24c], who constructed for any
large n a set of n points where any 4 points determine at least 5 distinct
distances, yet the number of distinct distances is O(n²/√(log n)).

The statement asserts the negative answer: there is no constant c > 0 and size bound N such that
every set of at least N points with the four-point-five-distance property determines at least
c · n² distinct distances.
-/
theorem erdos_problem_135 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card → FourPointFiveDist A →
        c * (A.card : ℝ) ^ 2 ≤ (numDistances A : ℝ) :=
  sorry

/--
Tao's construction [Ta24c] (PROVED, not checked here): for some constant C and every large n there
is a set of n points in the plane in which any four points determine at least five distinct
distances, and which determines at most C n² / √(log n) distinct distances in total.
-/
theorem erdos_problem_135.variants.tao :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧ FourPointFiveDist A ∧
        (numDistances A : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.sqrt (Real.log n) :=
  sorry

/--
The main theorem follows from Tao's construction (PROVED in Lean): for large n the distances
number at most C n² / √(log n), which is below c n² once √(log n) > C / c.
-/
theorem erdos_problem_135.variants.main_of_tao
    (htao : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∃ A : Finset (EuclideanSpace ℝ (Fin 2)), A.card = n ∧ FourPointFiveDist A ∧
        (numDistances A : ℝ) ≤ C * (n : ℝ) ^ 2 / Real.sqrt (Real.log n)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card → FourPointFiveDist A →
        c * (A.card : ℝ) ^ 2 ≤ (numDistances A : ℝ) := by
  rintro ⟨c, hc, N, hN⟩
  obtain ⟨C, hC, hev⟩ := htao
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog
  have h1 : ∀ᶠ n : ℕ in atTop, C / c < Real.sqrt (Real.log (n : ℝ)) :=
    hsq.eventually_gt_atTop _
  obtain ⟨n, ⟨A, hAcard, hA4, hAd⟩, hlt, hnN, hn2⟩ :=
    (hev.and (h1.and ((eventually_ge_atTop N).and (eventually_ge_atTop 2)))).exists
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqpos : 0 < Real.sqrt (Real.log (n : ℝ)) :=
    lt_trans (div_pos hC hc) hlt
  have hd : c * (n : ℝ) ^ 2 ≤ (numDistances A : ℝ) := by
    have := hN A (by omega) hA4
    rwa [hAcard] at this
  have h3 : c * (n : ℝ) ^ 2 ≤ C * (n : ℝ) ^ 2 / Real.sqrt (Real.log (n : ℝ)) := le_trans hd hAd
  rw [le_div_iff₀ hsqpos] at h3
  rw [div_lt_iff₀ hc] at hlt
  have hn2pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hlt hn2pos]

/--
The first pass's statement, without a size guard, is false for a trivial reason (PROVED in Lean):
the one-point set has no distances and vacuously has the four-point property, so
`c * 1 ≤ 0` fails for every `c > 0`. Its negation therefore says nothing about Tao's theorem, and
the main theorem carries the guard `N ≤ A.card`.
-/
theorem erdos_problem_135.variants.first_pass_false :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        FourPointFiveDist A →
        c * (A.card : ℝ) ^ 2 ≤ (numDistances A : ℝ) := by
  rintro ⟨c, hc, h⟩
  have hfp : FourPointFiveDist ({0} : Finset (EuclideanSpace ℝ (Fin 2))) := by
    intro S hS hcard
    exfalso
    have := Finset.card_le_card hS
    simp at this
    omega
  have hnd : numDistances ({0} : Finset (EuclideanSpace ℝ (Fin 2))) = 0 := by
    unfold numDistances
    rw [Finset.singleton_product_singleton, Finset.filter_singleton]
    simp
  have h1 := h {0} hfp
  rw [hnd] at h1
  simp at h1
  linarith

/--
Erdős's stronger conjecture [Er97b] (DISPROVED, as a consequence of the main theorem, not checked
here): every large set of $n$ points with the four-point-five-distance property contains a subset of
at least $c n$ points whose pairwise distances are all distinct. It is false, because it implies
the first question: $m$ points with all distances distinct determine $\binom m2$ distances.
-/
theorem erdos_problem_135.variants.stronger_conjecture_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ,
      ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
        N ≤ A.card → FourPointFiveDist A →
        ∃ B : Finset (EuclideanSpace ℝ (Fin 2)), B ⊆ A ∧ c * (A.card : ℝ) ≤ (B.card : ℝ) ∧
          ∀ p ∈ B, ∀ q ∈ B, ∀ r ∈ B, ∀ s ∈ B, p ≠ q → r ≠ s → dist p q = dist r s →
            (p = r ∧ q = s) ∨ (p = s ∧ q = r) :=
  sorry
