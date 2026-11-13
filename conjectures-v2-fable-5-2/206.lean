-- [AI - Claude Fable 5.2]: Erdős Problem 206 — second-pass formalization
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

open Finset BigOperators MeasureTheory

/-!
# Erdős Problem #206

*Source:* [erdosproblems.com/206](https://www.erdosproblems.com/206) (status **DISPROVED**: "This
has been solved in the negative."; captured 2026-02-20). [ErGr80, p.31]

Let $x>0$ be a real number. For any $n\geq 1$ let
$$R_n(x) = \sum_{i=1}^n\frac{1}{m_i}<x$$
be the maximal sum of $n$ distinct unit fractions which is $<x$.

Is it true that, for almost all $x$, for sufficiently large $n$, we have
$$R_{n+1}(x)=R_n(x)+\frac{1}{m},$$
where $m$ is minimal such that $m$ does not appear in $R_n(x)$ and the right-hand side is $<x$?
(That is, are the best underapproximations eventually always constructed in a 'greedy' fashion?)

Remarks recorded on the page (abridged): Erdős and Graham write it is 'not difficult' to construct
irrational $x$ such that this fails (although give no proof or reference). Curtiss [Cu22] showed
that this is true for $x=1$ and Erdős [Er50b] showed it is true for all $x=1/m$ with $m\geq 1$.
Nathanson [Na23] has shown it is true for $x=a/b$ when $a\mid b+1$ and Chu [Ch23b] has shown it is
true for a larger class of rationals; it is still unknown whether this is true for all rational
$x>0$. Without the 'eventually' condition this can fail for some rational $x$; for example
$R_1(\tfrac{11}{24})=\frac{1}{3}$ but $R_2(\tfrac{11}{24})=\frac{1}{4}+\frac{1}{5}$. Kovač [Ko24b]
has proved that this is false - in fact as false as possible: the set of $x\in (0,\infty)$ for
which the best underapproximations are eventually 'greedy' has Lebesgue measure zero. (It remains
an open problem to give any explicit example of a number which is not eventually greedy.) See also
[282].

## Status after capture

The metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12) lists the problem as
**disproved (Lean)** since 2026-04-28. Upstream `formal-conjectures` (`5258ab9`) states the negative
answer in the weak form `¬ ∀ᵐ x > 0, EventuallyGreedy x`, with a linked Lean proof. The main theorem
below is Kovač's stronger measure-zero statement, as the page records it. Neither [Ko24b] nor the
Lean proof was read in this review.

## Encoding notes

* The theorem states Kovač's result. It implies the negative answer to the question as asked,
  `¬ ∀ᵐ x > 0, IsEventuallyGreedy x` (`erdos_problem_206.not_ae_of_main`, PROVED in Lean).
* `bestUnderapprox n x` is an `sSup` over a set that is bounded above by `x` and, for `x > 0`,
  nonempty (`bddAbove`, `exists_underapprox`, PROVED in Lean); so it is the supremum of the sums
  and every admissible sum is at most it (`le_bestUnderapprox`). That the supremum is attained is
  argued in the review and not proved in Lean. The guard `0 < x` in the theorem matters: for
  `x ≤ 0` the set is empty and `IsEventuallyGreedy x` holds vacuously.
* The page's example is PROVED under these definitions: `R_1(11/24) = 1/3`,
  `R_2(11/24) = 1/4 + 1/5 = 9/20`, and no `1/3 + 1/k` equals `R_2(11/24)`
  (`bestUnderapprox_one_eleven_24`, `bestUnderapprox_two_eleven_24`, `not_greedy_eleven_24`).
* `IsEventuallyGreedy` quantifies over *every* `n`-set attaining `R_n(x)`. The page's wording
  ("`m` does not appear in `R_n(x)`") presupposes one representation, and upstream uses a single
  increasing chain of denominators. The chain reading is added as `IsEventuallyGreedyChain` with
  the corresponding statement `variants.kovac_chain` (SOLVED; not proved here). The input's set is
  contained in the chain set (review, Part A), so the main theorem follows from that variant.

## References

From the site's `/latex/206` bibliography:
* [Ch23b] Chu, H. V., _A threshold for the best two-term underapproximation by Egyptian
  fractions_. arXiv:2306.12564 (2023).
* [Cu22] Curtiss, D. R., _On Kellogg's Diophantine Problem_. Amer. Math. Monthly (1922), 380–387.
* [Er50b] Erdős, Pál, _On a Diophantine equation_. Mat. Lapok (1950), 192–210.
* [Ko24b] Kovač, V., _On eventually greedy best underapproximations by Egyptian fractions_.
  arXiv:2406.07218 (2024).
* [Na23] Nathanson, M., _Underapproximation by Egyptian fractions_. J. Number Theory (2023),
  208–234.

From other problems' site bibliographies:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.) The
  page cites p. 31.

*Provenance:* second pass of `conjectures/206.lean` (Fable 5.2 review,
`fable-5-2-review/206.md`).
-/

noncomputable section

/--
The sum of unit fractions with denominators from a finset of naturals:
∑_{m ∈ S} 1/m.
-/
def unitFracSum (S : Finset ℕ) : ℝ :=
  ∑ m ∈ S, (1 : ℝ) / (m : ℝ)

/--
R_n(x): the maximal sum of n distinct unit fractions (with positive integer
denominators) that is strictly less than x.
-/
def bestUnderapprox (n : ℕ) (x : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, 0 < m) ∧
    s = unitFracSum S ∧ s < x}

/--
A real number x > 0 is "eventually greedy" if there exists N₀ such that for
all n ≥ N₀, every set S of n distinct positive integers achieving R_n(x) can
be extended to achieve R_{n+1}(x) by adding the smallest eligible new
denominator.
-/
def IsEventuallyGreedy (x : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ S : Finset ℕ,
      S.card = n →
      (∀ m ∈ S, 0 < m) →
      unitFracSum S < x →
      unitFracSum S = bestUnderapprox n x →
        ∃ k : ℕ, 0 < k ∧ k ∉ S ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) < x ∧
          unitFracSum S + (1 : ℝ) / (k : ℝ) = bestUnderapprox (n + 1) x ∧
          (∀ j : ℕ, 0 < j → j ∉ S →
            unitFracSum S + (1 : ℝ) / (j : ℝ) < x → k ≤ j)

/--
Erdős Problem #206 (Disproved by Kovač [Ko24b]) [ErGr80, p.31]:

Let x > 0 be a real number. For any n ≥ 1 let R_n(x) be the maximal sum of n
distinct unit fractions which is < x. Erdős and Graham asked whether, for
almost all x, the best underapproximations are eventually constructed in a
greedy fashion: R_{n+1}(x) = R_n(x) + 1/m where m is the smallest new
denominator keeping the sum below x.

Kovač proved this is false — the set of x ∈ (0,∞) for which the best
underapproximations are eventually greedy has Lebesgue measure zero.

We formalize Kovač's result (the negation of the original conjecture).
-/
theorem erdos_problem_206 :
    volume {x : ℝ | 0 < x ∧ IsEventuallyGreedy x} = 0 :=
  sorry

/-- The set defining `bestUnderapprox n x` is bounded above by `x` (PROVED in Lean). -/
theorem erdos_problem_206.bddAbove (n : ℕ) (x : ℝ) :
    BddAbove {s : ℝ | ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, 0 < m) ∧
      s = unitFracSum S ∧ s < x} :=
  ⟨x, fun _ ⟨_, _, _, _, hs⟩ => hs.le⟩

/-- For `x > 0` and every `n` there are `n` distinct unit fractions with sum `< x`
(PROVED in Lean): take the denominators `M + 1, …, M + n` with `M > n / x`. -/
theorem erdos_problem_206.exists_underapprox {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧ (∀ m ∈ S, 0 < m) ∧ unitFracSum S < x := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((n : ℝ) / x)
  have hcard : (Finset.Icc (M + 1) (M + n)).card = n := by
    rw [Nat.card_Icc]
    omega
  refine ⟨Finset.Icc (M + 1) (M + n), hcard, fun m hm => ?_, ?_⟩
  · have := (Finset.mem_Icc.1 hm).1
    omega
  · have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hbound : ∀ m ∈ Finset.Icc (M + 1) (M + n), (1 : ℝ) / (m : ℝ) ≤ 1 / ((M : ℝ) + 1) := by
      intro m hm
      have h1 : (M : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hm).1
      exact one_div_le_one_div_of_le hM1 h1
    have hsum := Finset.sum_le_card_nsmul _ _ _ hbound
    rw [hcard, nsmul_eq_mul] at hsum
    have h2 : (n : ℝ) * (1 / ((M : ℝ) + 1)) < x := by
      rw [mul_one_div, div_lt_iff₀ hM1]
      have h3 := (div_lt_iff₀ hx).1 hM
      nlinarith
    exact lt_of_le_of_lt hsum h2

/-- Every admissible sum is at most `R_n(x)` (PROVED in Lean). -/
theorem erdos_problem_206.le_bestUnderapprox {n : ℕ} {x : ℝ} {S : Finset ℕ} (hS : S.card = n)
    (hpos : ∀ m ∈ S, 0 < m) (hlt : unitFracSum S < x) :
    unitFracSum S ≤ bestUnderapprox n x :=
  le_csSup (erdos_problem_206.bddAbove n x) ⟨S, hS, hpos, rfl, hlt⟩

/-- `R_n(x) ≤ x` for `x > 0` (PROVED in Lean). -/
theorem erdos_problem_206.bestUnderapprox_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    bestUnderapprox n x ≤ x := by
  obtain ⟨S, hS, hpos, hlt⟩ := erdos_problem_206.exists_underapprox hx n
  exact csSup_le ⟨_, S, hS, hpos, rfl, hlt⟩ fun _ ⟨_, _, _, _, hs⟩ => hs.le

/-- The page's example (PROVED in Lean): `R_1(11/24) = 1/3`. -/
theorem erdos_problem_206.bestUnderapprox_one_eleven_24 :
    bestUnderapprox 1 (11 / 24) = 1 / 3 := by
  have hmem : (1 / 3 : ℝ) ∈ {s : ℝ | ∃ S : Finset ℕ, S.card = 1 ∧ (∀ m ∈ S, 0 < m) ∧
      s = unitFracSum S ∧ s < 11 / 24} :=
    ⟨{3}, rfl, fun m hm => by simp at hm; omega, by simp [unitFracSum], by norm_num⟩
  apply le_antisymm
  · refine csSup_le ⟨_, hmem⟩ ?_
    rintro s ⟨S, hS, hpos, rfl, hlt⟩
    obtain ⟨m, rfl⟩ := Finset.card_eq_one.1 hS
    have hm := hpos m (by simp)
    have hsum : unitFracSum {m} = 1 / (m : ℝ) := by simp [unitFracSum]
    rw [hsum] at hlt ⊢
    have hm3 : 3 ≤ m := by
      by_contra hcon
      have hm2 : m ≤ 2 := by omega
      interval_cases m <;> norm_num at hlt
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm3)
  · exact le_csSup (erdos_problem_206.bddAbove 1 _) hmem

/-- Two unit fractions `1/a + 1/b < 11/24` with `a < b` have sum at most `9/20`
(PROVED in Lean). -/
theorem erdos_problem_206.pair_le (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (h : 1 / (a : ℝ) + 1 / (b : ℝ) < 11 / 24) : 1 / (a : ℝ) + 1 / (b : ℝ) ≤ 9 / 20 := by
  have hbn : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
  rcases Nat.lt_or_ge a 5 with ha5 | ha5
  · interval_cases a
    · exfalso
      push_cast at h
      linarith
    · exfalso
      push_cast at h
      linarith
    · have hb9 : 9 ≤ b := by
        by_contra hcon
        have hb8 : b ≤ 8 := by omega
        interval_cases b <;> norm_num at h
      have h1 : 1 / (b : ℝ) ≤ 1 / 9 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb9)
      push_cast
      linarith
    · have h1 : 1 / (b : ℝ) ≤ 1 / 5 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 5 ≤ b by omega))
      push_cast
      linarith
  · have h1 : 1 / (a : ℝ) ≤ 1 / 5 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast ha5)
    have h2 : 1 / (b : ℝ) ≤ 1 / 6 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 6 ≤ b by omega))
    linarith

/-- The page's example (PROVED in Lean): `R_2(11/24) = 1/4 + 1/5 = 9/20`. -/
theorem erdos_problem_206.bestUnderapprox_two_eleven_24 :
    bestUnderapprox 2 (11 / 24) = 9 / 20 := by
  have hmem : (9 / 20 : ℝ) ∈ {s : ℝ | ∃ S : Finset ℕ, S.card = 2 ∧ (∀ m ∈ S, 0 < m) ∧
      s = unitFracSum S ∧ s < 11 / 24} := by
    refine ⟨{4, 5}, rfl, fun m hm => ?_, ?_, by norm_num⟩
    · simp at hm
      omega
    · rw [unitFracSum, Finset.sum_pair (by norm_num)]
      norm_num
  apply le_antisymm
  · refine csSup_le ⟨_, hmem⟩ ?_
    rintro s ⟨S, hS, hpos, rfl, hlt⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hS
    have hsum : unitFracSum {a, b} = 1 / (a : ℝ) + 1 / (b : ℝ) := by
      rw [unitFracSum, Finset.sum_pair hab]
    rw [hsum] at hlt ⊢
    have ha := hpos a (by simp)
    have hb := hpos b (by simp)
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact erdos_problem_206.pair_le a b ha h hlt
    · rw [add_comm] at hlt ⊢
      exact erdos_problem_206.pair_le b a hb h hlt
  · exact le_csSup (erdos_problem_206.bddAbove 2 _) hmem

/-- The page's example (PROVED in Lean): the best one-term underapproximation `1/3` of `11/24`
cannot be extended to the best two-term one; no `1/3 + 1/k` equals `R_2(11/24) = 9/20`. So the
greedy step fails at `n = 1`. -/
theorem erdos_problem_206.not_greedy_eleven_24 (k : ℕ) :
    unitFracSum {3} + 1 / (k : ℝ) ≠ bestUnderapprox 2 (11 / 24) := by
  rw [erdos_problem_206.bestUnderapprox_two_eleven_24]
  intro h
  have h3 : unitFracSum {3} = 1 / 3 := by simp [unitFracSum]
  rw [h3] at h
  have hk : 1 / (k : ℝ) = 7 / 60 := by linarith
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hk
    norm_num at hk
  have h7 : (7 : ℝ) * (k : ℝ) = 60 := by
    field_simp at hk
    linarith
  have h8 : 7 * k = 60 := by exact_mod_cast h7
  omega

/-- Kovač's measure-zero statement implies the negative answer to the question as asked
(PROVED in Lean): it is not the case that almost every `x > 0` is eventually greedy. -/
theorem erdos_problem_206.not_ae_of_main
    (h : volume {x : ℝ | 0 < x ∧ IsEventuallyGreedy x} = 0) :
    ¬ ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), IsEventuallyGreedy x := by
  intro hae
  rw [ae_restrict_iff' measurableSet_Ioi, ae_iff] at hae
  have hsub : Set.Ioi (0 : ℝ) ⊆ {x : ℝ | 0 < x ∧ IsEventuallyGreedy x} ∪
      {x : ℝ | ¬(x ∈ Set.Ioi (0 : ℝ) → IsEventuallyGreedy x)} := by
    intro x hx
    by_cases hg : IsEventuallyGreedy x
    · exact Or.inl ⟨hx, hg⟩
    · exact Or.inr fun h' => hg (h' hx)
  have h1 := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [h, hae, Real.volume_Ioi, add_zero] at h1
  exact absurd h1 (by simp)

/-- The chain reading of "eventually greedy" (upstream's): from some `N₀` on, the best `n`-term
underapproximations are the prefixes of one strictly increasing sequence of denominators. (Added in
the second pass.) -/
def IsEventuallyGreedyChain (x : ℝ) : Prop :=
  ∃ m : ℕ → ℕ, StrictMono m ∧ (∀ i, 0 < m i) ∧ ∃ N₀ : ℕ, ∀ n ≥ N₀,
    unitFracSum ((Finset.range n).image m) < x ∧
    unitFracSum ((Finset.range n).image m) = bestUnderapprox n x

/-- Kovač's theorem [Ko24b] for the chain reading (SOLVED; not proved here). The set of the main
theorem is contained in this one (argued in the review, not proved in Lean), so this statement
implies the main theorem. -/
theorem erdos_problem_206.variants.kovac_chain :
    volume {x : ℝ | 0 < x ∧ IsEventuallyGreedyChain x} = 0 :=
  sorry

end
