-- [AI - Claude Sonnet 5.5]: Erdős Problem 140 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Real Filter

noncomputable section

/-!
# Erdős Problem #140: Roth's Theorem with a Polylogarithmic Saving

*Source:* [erdosproblems.com/140](https://www.erdosproblems.com/140) (banner **PROVED**, prize
**\$500**: "This has been solved in the affirmative."; page last edited 20 December 2025; captured
2026-02-20 as the tidied problem box). [ErGr80, p.11] [Er81] [Er97c]

Let $r_3(N)$ be the size of the largest subset of $\{1,\ldots,N\}$ which does not contain a
non-trivial $3$-term arithmetic progression. Prove that $r_3(N)\ll N/(\log N)^C$ for every $C>0$.

Remarks recorded on the page:
* Proved by Kelley and Meka [KeMe23]. In [ErGr80] and [Er81] it is conjectured that this holds for
  every $k$-term arithmetic progression.
* See also [3].

Tags: additive combinatorics, arithmetic progressions. OEIS: A003002. 0 comments at capture.

**Status.** PROVED. The mirror (`teorth/erdosproblems`) has `proved` since 2025-08-31 and
`proved (Lean)` since 2026-08-24, which records a Lean proof after the capture. It was not examined.
Upstream has no `140.lean` at the pinned snapshot. The main theorem asserts the true statement and is
`sorry` here, since the Kelley–Meka theorem is not in Mathlib.

**Encoding.**
* `IsThreeAPFree S` is Mathlib's `ThreeAPFree` for the finite set `S ⊆ ℕ`
  (`variants.isThreeAPFree_iff_threeAPFree`). The condition `a + c = 2 * b → a = b` excludes exactly the
  trivial progressions, and it is the same as "no `a` and `d > 0` with `a`, `a + d`, `a + 2 * d` in `S`"
  (`variants.isThreeAPFree_iff_isAPFree`).
* `r3 N` is the `sSup` of the sizes of the 3-progression-free subsets of `{1, …, N}`. The set of sizes
  contains `0` and is bounded by `N`, so `sSup` is its maximum and there is no junk value
  (`card_le_r3`).
* The main theorem says that for every `C > 0` there is `K > 0` with `r3 N ≤ K * N / (log N) ^ C` for all
  large `N`. This is $r_3(N)\ll_C N/(\log N)^C$. The power is real, and for `N ≥ 2` its base is positive.
  "For all large `N`" absorbs the finitely many `N` where `log N = 0`.
* `variants.main_of_exp_bound` proves that any bound `r3 N ≤ N * exp (-c * (log N) ^ δ)` with `c, δ > 0`
  implies the main theorem. Kelley and Meka's bound has this shape. The page does not state its
  exponent, so none is asserted here.
* `variants.k_term` is the page's conjecture for every $k$-term progression, stated with `IsAPFree` and
  `rk`. For `k = 3` it is the main theorem (`variants.r3_eq_rk_three`).
* `variants.r3_fourteen_ge` proves $r_3(14)\ge8$ from an explicit set.

## References

* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathématique (1980). The page cites p. 11.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [KeMe23] Kelley, Z. and Meka, R., _Strong bounds for 3-progressions_. arXiv:2302.05537 (2023).
* [3] The page's cross-reference to Problem 3.

(Provenance: [ErGr80], [Er81] and [KeMe23] are from the `/latex/140` fetch in the session logs. [Er97c]
is in the page's heading but not in that fetch's output, and is from the bibliographies of the `/latex`
pages of other problems.)
-/

/-- A finite set S ⊆ ℕ is 3-AP-free if it contains no non-trivial 3-term
    arithmetic progression: for all a, b, c ∈ S satisfying a + c = 2 * b,
    a = b holds (which forces a = b = c, i.e., the progression is trivial). -/
def IsThreeAPFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = b

/-- r₃(N) is the maximum size of a 3-AP-free subset of {1, ..., N}. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset ℕ,
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
    IsThreeAPFree S ∧
    S.card = k }

/--
Erdős Problem #140 [ErGr80, Er81, Er97c] — PROVED (\$500):
Let r₃(N) be the size of the largest subset of {1, ..., N} containing no
non-trivial 3-term arithmetic progression. Then r₃(N) ≪ N / (log N)^C
for every C > 0.

Formally: for every C > 0 there exists a constant K > 0 such that
  r₃(N) ≤ K * N / (log N)^C  for all sufficiently large N.

Proved by Kelley and Meka [KeMe23].
-/
theorem erdos_problem_140 :
    ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C :=
  sorry

/-- Every 3-AP-free subset of `{1, …, N}` has at most `r3 N` elements (PROVED in Lean). -/
theorem erdos_problem_140.card_le_r3 {N : ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, 1 ≤ x ∧ x ≤ N)
    (hf : IsThreeAPFree S) : S.card ≤ r3 N := by
  unfold r3
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro m ⟨T, hT, _, rfl⟩
    have hsub : T ⊆ Finset.Icc 1 N := fun x hx => Finset.mem_Icc.mpr (hT x hx)
    simpa using Finset.card_le_card hsub
  · exact ⟨S, hS, hf, rfl⟩

/-- `IsThreeAPFree` is Mathlib's `ThreeAPFree` (PROVED in Lean). -/
theorem erdos_problem_140.variants.isThreeAPFree_iff_threeAPFree (S : Finset ℕ) :
    IsThreeAPFree S ↔ ThreeAPFree (S : Set ℕ) := by
  constructor
  · intro h a ha b hb c hc habc
    exact h a ha b hb c hc (by omega)
  · intro h a ha b hb c hc habc
    exact h ha hb hc (by omega)

/--
The Kelley–Meka bound has the shape that implies the main theorem (PROVED in Lean): if
`r3 N ≤ N * exp (-c * (log N) ^ δ)` for all large `N`, with `c, δ > 0`, then
`r3 N ≤ N / (log N) ^ C` for all large `N`, for every `C > 0`. The proof uses that
`exp (c z) / z ^ s → ∞`.
-/
theorem erdos_problem_140.variants.main_of_exp_bound (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (h : ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ δ)) :
    ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C := by
  intro C hC
  refine ⟨1, one_pos, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun N : ℕ => (Real.log (N : ℝ)) ^ δ) atTop atTop :=
    (tendsto_rpow_atTop hδ).comp hlog
  have hexp := tendsto_exp_mul_div_rpow_atTop (C / δ) c hc
  have h1 : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.exp (c * (Real.log (N : ℝ)) ^ δ) / ((Real.log (N : ℝ)) ^ δ) ^ (C / δ) :=
    hz.eventually (hexp.eventually (eventually_ge_atTop 1))
  have h2 : ∀ᶠ N : ℕ in atTop, 1 < Real.log (N : ℝ) := hlog.eventually (eventually_gt_atTop 1)
  filter_upwards [h, h1, h2] with N hN h1N h2N
  have hy : 0 < Real.log (N : ℝ) := by linarith
  have hz0 : 0 < (Real.log (N : ℝ)) ^ δ := Real.rpow_pos_of_pos hy δ
  have hzs : 0 < ((Real.log (N : ℝ)) ^ δ) ^ (C / δ) := Real.rpow_pos_of_pos hz0 _
  have e : ((Real.log (N : ℝ)) ^ δ) ^ (C / δ) = (Real.log (N : ℝ)) ^ C := by
    rw [← Real.rpow_mul hy.le, mul_div_cancel₀ _ hδ.ne']
  rw [e] at h1N hzs
  have hyC : 0 < (Real.log (N : ℝ)) ^ C := hzs
  have h3 : (Real.log (N : ℝ)) ^ C ≤ Real.exp (c * (Real.log (N : ℝ)) ^ δ) := by
    have := (le_div_iff₀ hyC).mp h1N
    linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  calc (r3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log (N : ℝ)) ^ δ) := hN
    _ = (N : ℝ) / Real.exp (c * (Real.log (N : ℝ)) ^ δ) := by
        rw [neg_mul, Real.exp_neg, div_eq_mul_inv]
    _ ≤ (N : ℝ) / (Real.log (N : ℝ)) ^ C := by
        apply div_le_div_of_nonneg_left hN0 hyC h3
    _ = 1 * (N : ℝ) / (Real.log (N : ℝ)) ^ C := by rw [one_mul]

/-- A finite set S ⊆ ℕ contains no k-term arithmetic progression a, a+d, …, a+(k-1)d with d > 0. -/
def IsAPFree (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ∃ i : ℕ, i < k ∧ a + i * d ∉ S

/-- r_k(N) is the maximum size of a k-AP-free subset of {1, ..., N}. -/
noncomputable def rk (k N : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ S : Finset ℕ,
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
    IsAPFree k S ∧
    S.card = m }

/-- `IsThreeAPFree` is the case `k = 3` of `IsAPFree` (PROVED in Lean). -/
theorem erdos_problem_140.variants.isThreeAPFree_iff_isAPFree (S : Finset ℕ) :
    IsThreeAPFree S ↔ IsAPFree 3 S := by
  constructor
  · intro h a d hd
    by_contra hcon
    push_neg at hcon
    have h0 : a ∈ S := by simpa using hcon 0 (by norm_num)
    have h1 : a + d ∈ S := by simpa using hcon 1 (by norm_num)
    have h2 : a + 2 * d ∈ S := hcon 2 (by norm_num)
    have := h a h0 (a + d) h1 (a + 2 * d) h2 (by omega)
    omega
  · intro h x hx y hy z hz hxz
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨i, hi, hni⟩ := h x (y - x) (by omega)
      have e0 : x + 0 * (y - x) = x := by omega
      have e1 : x + 1 * (y - x) = y := by omega
      have e2 : x + 2 * (y - x) = z := by omega
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · rw [e0] at hni; exact hni hx
      · rw [e1] at hni; exact hni hy
      · rw [e2] at hni; exact hni hz
    · obtain ⟨i, hi, hni⟩ := h z (y - z) (by omega)
      have e0 : z + 0 * (y - z) = z := by omega
      have e1 : z + 1 * (y - z) = y := by omega
      have e2 : z + 2 * (y - z) = x := by omega
      rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · rw [e0] at hni; exact hni hz
      · rw [e1] at hni; exact hni hy
      · rw [e2] at hni; exact hni hx

/-- `r3` is `rk 3` (PROVED in Lean). -/
theorem erdos_problem_140.variants.r3_eq_rk_three (N : ℕ) : r3 N = rk 3 N := by
  unfold r3 rk
  congr 1
  ext m
  simp only [Set.mem_setOf_eq, erdos_problem_140.variants.isThreeAPFree_iff_isAPFree]

/--
The conjecture of [ErGr80] and [Er81] that the bound holds for every `k`-term progression (OPEN: the
page records no solution). For `k = 3` it is the main theorem.
-/
theorem erdos_problem_140.variants.k_term :
    ∀ k : ℕ, 3 ≤ k → ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (rk k N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C :=
  sorry

/-- $r_3(14)\ge8$ (PROVED in Lean), from the 3-AP-free set `{1, 2, 4, 5, 10, 11, 13, 14}`. -/
theorem erdos_problem_140.variants.r3_fourteen_ge : 8 ≤ r3 14 := by
  have hS : ∀ x ∈ ({1, 2, 4, 5, 10, 11, 13, 14} : Finset ℕ), 1 ≤ x ∧ x ≤ 14 := by decide
  have hf : IsThreeAPFree ({1, 2, 4, 5, 10, 11, 13, 14} : Finset ℕ) := by
    unfold IsThreeAPFree
    decide
  have := erdos_problem_140.card_le_r3 hS hf
  simpa using this

end
