-- [AI - Claude Sonnet 5.5]: Erdős Problem 139 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset
open Filter
open scoped Topology

/-!
# Erdős Problem #139: Szemerédi's Theorem, $r_k(N)=o(N)$

*Source:* [erdosproblems.com/139](https://www.erdosproblems.com/139) (banner **PROVED**, prize
**\$1000**: "This has been solved in the affirmative."; page last edited 23 January 2026; captured
2026-03-05 as the tidied problem box). [Er57] [Er61] [Er65b] [Er73] [Er75b] [Er76g] [Er80] [Er81]
[Er82e] [Er83c] [Er97c]

Let $r_k(N)$ be the size of the largest subset of $\{1,\ldots,N\}$ which does not contain a
non-trivial $k$-term arithmetic progression. Prove that $r_k(N)=o(N)$.

Remarks recorded on the page:
* A conjecture of Erdős and Turán. Proved by Szemerédi [Sz75]. The best known bounds are due to
  Kelley and Meka [KeMe23] for $k=3$ (with further slight improvements in [BlSi23]), Green and Tao
  [GrTa17] for $k=4$, and Leng, Sah, and Sawhney [LSS24] for $k\geq 5$.
* In [Er80] Erdős reports that Rothe-Ille was given the problem of estimating $r_k(n)$ by Schur in the
  1930s, and so 'perhaps Schur conjectured $r_k(N)=o(N)$ before Turán and myself'.
* See also [3].

Tags: additive combinatorics, arithmetic progressions. OEIS: A003002, A003003, A003004, A003005.
0 comments at capture.

**Status.** PROVED (Szemerédi's theorem). The mirror (`teorth/erdosproblems`) has `proved` since
2025-08-31 and `proved (Lean)` since 2026-08-23, which records a Lean proof after the capture. Upstream
has `erdos_139`, category `research solved`, with a link to a Lean proof in an external repository
(`plby/lean-proofs`). Neither was checked here. The main theorem asserts the true statement and is
`sorry` here, since Szemerédi's theorem is not in Mathlib. Its case $k=3$, Roth's theorem, is in
Mathlib, and `variants.k_eq_three` derives it from there.

**Encoding.**
* `APFree k S` says there are no `a` and `d > 0` with `a, a + d, …, a + (k - 1) * d` all in `S`. The
  start `a` ranges over ℕ, which does not matter for `S ⊆ range N`.
* The main theorem says that for every `k ≥ 3` and `ε > 0` there is `N₀` such that for all `N ≥ N₀`
  every `k`-progression-free `S ⊆ {0, …, N-1}` has at most `ε N` elements. That is $r_k(N)=o(N)$.
  The page uses $\{1,\ldots,N\}$, and a shift by one changes nothing.
  `variants.main_iff_littleO` proves that it is equivalent to `Tendsto (rk k N / N) atTop (𝓝 0)`, where
  `rk k N` is the largest size of such an `S`.
* The restriction `3 ≤ k` is harmless. For `k = 1` only `S = ∅` is free of progressions, and for
  `k = 2` only sets with at most one element, so $r_1=0$ and $r_2\le1$. `main_iff_littleO` holds for
  every `k ≥ 1`.
* The known bounds are named on the page without formulas, and are not formalized.
* `variants.rk_three_fourteen` proves $r_3(14)\ge8$ from the explicit set `{0, 1, 3, 4, 9, 10, 12, 13}`.
  A separate search (a C program, not part of this file) gives $r_3(N)$ for $N=1,\dots,30$ as
  1 2 2 3 4 4 4 4 5 5 6 6 7 8 8 8 8 8 8 9 9 9 9 10 10 11 11 11 11 12, so $r_3(14)=8$.

## References

* [Er57] Erdős, P., _Some unsolved problems_. Michigan Math. J. (1957), 291–300.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Er65b] Erdős, P., _Some recent advances and current problems in number theory_. Lectures on
  Modern Mathematics, Vol. III (1965), 196–244.
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A survey of
  combinatorial theory (1973), 117–138.
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques de
  Bordeaux (1975), 295–310.
* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math. (1980),
  89–115.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982), 59–79.
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [KeMe23] Kelley, Z. and Meka, R., _Strong bounds for 3-progressions_. arXiv:2302.05537 (2023).
* [BlSi23] Bloom, T. F. and Sisask, O., _An improvement to the Kelley–Meka bounds on three-term
  arithmetic progressions_. arXiv:2309.02353 (2023).
* [LSS24] Leng, J., Sah, A. and Sawhney, M. **DEFERRED:** no title or venue was recovered.
* [Sz75], [GrTa17], [Er76g]: cited on the page. **DEFERRED:** no bibliographic data was recovered.
* [3] The page's cross-reference to Problem 3.

(Provenance: [Er57] to [Er83c], [Er97c], [KeMe23] and [BlSi23] are from the bibliographies of the
`/latex` pages of other problems. **DEFERRED:** no `/latex/139` fetch exists in the logs, so the entries
were not checked against the page's own bibliography.)
-/

/--
A Finset S of natural numbers is free of non-trivial k-term arithmetic
progressions: there do not exist a, d with d ≥ 1 such that
{a, a+d, …, a+(k-1)d} ⊆ S.
-/
def APFree (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ∃ i : ℕ, i < k ∧ a + i * d ∉ S

/--
Erdős Problem #139 (Erdős–Turán conjecture / Szemerédi's theorem) [Er57, Er61, Er65b, Er73, Er75b,
Er76g, Er80, Er81, Er82e, Er83c, Er97c] — PROVED (\$1000):

For every k ≥ 3 and every ε > 0, there exists N₀ such that for all N ≥ N₀,
every subset of {0, …, N-1} with no non-trivial k-term arithmetic progression
has size at most ε * N.

Equivalently, r_k(N) = o(N).

Proved by Szemerédi [Sz75].
-/
theorem erdos_problem_139
    (k : ℕ) (hk : 3 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → APFree k S →
        (S.card : ℝ) ≤ ε * (N : ℝ) :=
  sorry

/-- `r_k(N)`: the size of the largest `S ⊆ {0, …, N-1}` with `APFree k S`. -/
noncomputable def rk (k N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).powerset.filter (fun S => APFree k S)).sup Finset.card

/-- Every progression-free subset of `{0, …, N-1}` has at most `rk k N` elements (PROVED in Lean). -/
theorem erdos_problem_139.card_le_rk {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N)
    (hf : APFree k S) : S.card ≤ rk k N := by
  classical
  unfold rk
  exact Finset.le_sup (f := Finset.card) (by simp [hS, hf])

/-- For `k ≥ 1` some progression-free subset of `{0, …, N-1}` has exactly `rk k N` elements
(PROVED in Lean). -/
theorem erdos_problem_139.exists_rk (k N : ℕ) (hk : 1 ≤ k) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ APFree k S ∧ S.card = rk k N := by
  classical
  have hne : ((Finset.range N).powerset.filter (fun S => APFree k S)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    intro a d hd
    exact ⟨0, by omega, by simp⟩
  obtain ⟨S, hS, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  simp only [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, hS.1, hS.2, ?_⟩
  unfold rk
  convert hsup.symm

/--
The main statement is $r_k(N)=o(N)$ (PROVED in Lean): for `k ≥ 1`, the statement of
`erdos_problem_139` for all `ε > 0` is equivalent to `r_k(N) / N → 0`.
-/
theorem erdos_problem_139.variants.main_iff_littleO (k : ℕ) (hk : 1 ≤ k) :
    (∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → APFree k S → (S.card : ℝ) ≤ ε * (N : ℝ)) ↔
    Tendsto (fun N : ℕ => (rk k N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := h (ε / 2) (by positivity)
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hNpos : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast this
    obtain ⟨S, hS, hf, hcard⟩ := erdos_problem_139.exists_rk k N hk
    have h1 := hN₀ N (le_trans (le_max_left _ _) hN) S hS hf
    rw [hcard] at h1
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
    nlinarith
  · intro h ε hε
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨max N₀ 1, fun N hN S hS hf => ?_⟩
    have hNpos : (0 : ℝ) < N := by
      have : 1 ≤ N := le_trans (le_max_right _ _) hN
      exact_mod_cast this
    have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos] at h1
    have h2 : (S.card : ℝ) ≤ (rk k N : ℝ) := by exact_mod_cast erdos_problem_139.card_le_rk hS hf
    linarith

/--
For `k = 3`, `APFree` is Mathlib's `ThreeAPFree` (PROVED in Lean): no `a`, `d > 0` with `a`, `a + d`,
`a + 2 d` in `S` is the same as `x + z = y + y → x = y` for `x, y, z ∈ S`.
-/
theorem erdos_problem_139.apfree_three_iff (S : Finset ℕ) :
    APFree 3 S ↔ ThreeAPFree (S : Set ℕ) := by
  constructor
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
  · intro h a d hd
    by_contra hcon
    push_neg at hcon
    have h0 : a ∈ S := by simpa using hcon 0 (by norm_num)
    have h1 : a + d ∈ S := by simpa using hcon 1 (by norm_num)
    have h2 : a + 2 * d ∈ S := hcon 2 (by norm_num)
    have := h (Finset.mem_coe.mpr h0) (Finset.mem_coe.mpr h1) (Finset.mem_coe.mpr h2) (by omega)
    omega

/--
The case `k = 3` of the main theorem is Roth's theorem, and it is PROVED in Lean from Mathlib's
`roth_3ap_theorem_nat` with `N₀ = cornersTheoremBound (ε / 3)`.
-/
theorem erdos_problem_139.variants.k_eq_three (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℕ, S ⊆ Finset.range N → APFree 3 S →
        (S.card : ℝ) ≤ ε * (N : ℝ) := by
  refine ⟨cornersTheoremBound (ε / 3), fun N hN S hS hfree => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact roth_3ap_theorem_nat ε hε hN S hS hlt.le
    ((erdos_problem_139.apfree_three_iff S).mp hfree)

/--
For `k ≥ 2` and `S ⊆ {0, …, N-1}`, progression-freeness can be checked with `a, d < N`
(PROVED in Lean).
-/
theorem erdos_problem_139.APFree_iff_bounded {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N)
    (hk : 2 ≤ k) :
    APFree k S ↔ ∀ a < N, ∀ d < N, 0 < d → ∃ i < k, a + i * d ∉ S := by
  constructor
  · intro h a _ d _ hd
    exact h a d hd
  · intro h a d hd
    by_cases ha : a < N
    · by_cases hd' : d < N
      · exact h a ha d hd' hd
      · exact ⟨1, by omega, fun hmem => by have := Finset.mem_range.mp (hS hmem); omega⟩
    · exact ⟨0, by omega, fun hmem => by have := Finset.mem_range.mp (hS hmem); omega⟩

/-- `{0, 1, 3, 4, 9, 10, 12, 13}` has no 3-term progression (PROVED in Lean by `decide`). -/
theorem erdos_problem_139.variants.apfree_three_example :
    APFree 3 ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ) := by
  have hS : ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ) ⊆ Finset.range 14 := by decide
  rw [erdos_problem_139.APFree_iff_bounded hS (by norm_num)]
  decide

/-- $r_3(14)\ge8$ (PROVED in Lean), from the 8-element set `{0, 1, 3, 4, 9, 10, 12, 13}`. -/
theorem erdos_problem_139.variants.rk_three_fourteen : 8 ≤ rk 3 14 := by
  have hS : ({0, 1, 3, 4, 9, 10, 12, 13} : Finset ℕ) ⊆ Finset.range 14 := by decide
  have := erdos_problem_139.card_le_rk hS erdos_problem_139.variants.apfree_three_example
  simpa using this
