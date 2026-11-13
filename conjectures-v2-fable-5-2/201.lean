-- [AI - Claude Fable 5.2]: Erdős Problem 201 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Erdős Problem #201

*Source:* [erdosproblems.com/201](https://www.erdosproblems.com/201) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-02-20). [Er73] [Er75b]
[ErGr79] [ErGr80]

Let $G_k(N)$ be such that any set of $N$ integers contains a subset of size at least $G_k(N)$
which does not contain a $k$-term arithmetic progression. Determine the size of $G_k(N)$. How
does it relate to $R_k(N)$, the size of the largest subset of $\{1,\ldots,N\}$ without a $k$-term
arithmetic progression? Is it true that
$$\lim_{N\to \infty}\frac{R_3(N)}{G_3(N)}=1?$$

Remarks recorded on the page: first asked and investigated by Riddell [Ri69]. It is trivial that
$G_k(N)\leq R_k(N)$, and it is possible that $G_k(N) <R_k(N)$ (for example $G_3(5)=3$ and
$R_3(5)=4$, and $G_3(14)\leq 7$ and $R_3(14)=8$). Komlós, Sulyok, and Szemerédi [KSS75] have
shown that $R_k(N) \ll_k G_k(N)$. OEIS A003002–A003005.

## Status

OPEN at capture and in the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12). Upstream
`formal-conjectures` (`5258ab9`) has no file for this problem.

## Encoding notes

* The main theorem asserts the "yes" answer to the page's last question (OPEN; corpus convention
  for open yes/no questions). The page records no belief either way.
* The input avoids defining $G_k(N)$. This file adds `G_ap k N`, the minimum over all `N`-element
  sets `S ⊆ ℤ` of the size of the largest `k`-AP-free subset of `S`, and proves:
  the main statement is equivalent to `(1 - ε) R_3(N) ≤ G_3(N)` for large `N`
  (`erdos_problem_201.iff_G_form`, PROVED in Lean) and to the page's literal limit
  `R_3(N) / G_3(N) → 1` (`erdos_problem_201.iff_limit`, PROVED in Lean).
* `G_k(N) ≤ R_k(N)` (`G_ap_le_R_ap`) and `G_3(N) ≥ 1` for `N ≥ 1` (`one_le_G_ap`) are PROVED, so
  the quotient in the limit is a quotient by a positive number for `N ≥ 1`.
* The page's value `R_3(5) = 4` is PROVED under the input's definitions (`R_ap_three_five`).
  `G_3(5) = 3`, `R_3(14) = 8` and `G_3(14) ≤ 7` were checked by computation only (see the review).
* The first two questions on the page ("Determine the size of $G_k(N)$. How does it relate to
  $R_k(N)$?") are not yes/no questions; the recorded partial answer [KSS75] is stated as
  `erdos_problem_201.variants.kss`.

## References

From the site's `/latex/201` bibliography:
* [KSS75] Komlós, J., Sulyok, M. and Szemerédi, E., _Linear problems in combinatorial number
  theory_. Acta Math. Acad. Sci. Hungar. (1975), 113–121.
* [Ri69] Riddell, J., _On sets of numbers containing no l terms in arithmetic progression_.
  Nieuw Arch. Wisk. (3) (1969), 204–209.

From other problems' site bibliographies (the page's heading keys are not in `/latex/201`):
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138. (Site `/latex/783` and others.)
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310.
  (Site `/latex/656` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/201.lean` (Fable 5.2 review,
`fable-5-2-review/201.md`).
-/

noncomputable section
open Classical

/-- A finset of integers contains a k-term arithmetic progression if there
    exist integers a, d with d ≠ 0 such that a + i·d ∈ S for all 0 ≤ i < k. -/
def HasKTermAP (k : ℕ) (S : Finset ℤ) : Prop :=
  ∃ a d : ℤ, d ≠ 0 ∧ ∀ i : Fin k, (a + (i.val : ℤ) * d) ∈ S

/-- The maximum cardinality of a subset of S that contains no k-term AP. -/
def maxAPFreeSize (k : ℕ) (S : Finset ℤ) : ℕ :=
  Finset.sup (S.powerset.filter (fun T => ¬HasKTermAP k T)) Finset.card

/-- R_k(N): the size of the largest subset of {1,...,N} without a k-term AP. -/
def R_ap (k N : ℕ) : ℕ :=
  maxAPFreeSize k (Finset.Icc (1 : ℤ) (N : ℤ))

/--
Erdős Problem #201 [Er73, Er75b, ErGr79, ErGr80]:

Is it true that lim_{N→∞} R_3(N) / G_3(N) = 1?

Since G_k(N) ≤ R_k(N) always holds, the question is equivalent to:
for every ε > 0, for all sufficiently large N, every set of N integers
contains a 3-AP-free subset of size at least (1 - ε) · R_3(N).

Status: OPEN; the "yes" direction is asserted. The equivalence with the limit is PROVED in Lean
below (`erdos_problem_201.iff_limit`).
-/
theorem erdos_problem_201 :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, S.card = N →
        ∃ T ⊆ S, ¬HasKTermAP 3 T ∧
          (1 - ε) * (R_ap 3 N : ℝ) ≤ (T.card : ℝ) := by
  sorry

/-- `G_k(N)`: the largest `m` such that every set of `N` integers contains a `k`-AP-free subset of
size at least `m`; that is, the minimum of `maxAPFreeSize k S` over the `N`-element sets `S ⊆ ℤ`.
(Added in the second pass; the input does not define it.) -/
def G_ap (k N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ S : Finset ℤ, S.card = N ∧ maxAPFreeSize k S = m}

/-- Every `k`-AP-free subset of `S` has at most `maxAPFreeSize k S` elements (PROVED in Lean). -/
theorem erdos_problem_201.card_le_maxAPFreeSize {k : ℕ} {S T : Finset ℤ} (hTS : T ⊆ S)
    (hT : ¬HasKTermAP k T) : T.card ≤ maxAPFreeSize k S :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hTS, hT⟩)

/-- The empty set contains no `k`-term progression when `k ≥ 1` (PROVED in Lean). For `k = 0`
every set "contains" one, and `maxAPFreeSize 0 S` is the junk value `0`. -/
theorem erdos_problem_201.not_hasKTermAP_empty {k : ℕ} (hk : 1 ≤ k) : ¬HasKTermAP k ∅ := by
  rintro ⟨a, d, -, h⟩
  simpa using h ⟨0, hk⟩

/-- For `k ≥ 1` the supremum defining `maxAPFreeSize k S` is attained (PROVED in Lean). -/
theorem erdos_problem_201.exists_card_eq_maxAPFreeSize {k : ℕ} (hk : 1 ≤ k) (S : Finset ℤ) :
    ∃ T ⊆ S, ¬HasKTermAP k T ∧ T.card = maxAPFreeSize k S := by
  have hne : (S.powerset.filter (fun T => ¬HasKTermAP k T)).Nonempty :=
    ⟨∅, Finset.mem_filter.2
      ⟨Finset.empty_mem_powerset S, erdos_problem_201.not_hasKTermAP_empty hk⟩⟩
  obtain ⟨T, hT, hsup⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hT
  exact ⟨T, hT.1, hT.2, hsup.symm⟩

/-- `{1, …, N} ⊆ ℤ` has `N` elements (PROVED in Lean). -/
theorem erdos_problem_201.card_Icc (N : ℕ) : (Finset.Icc (1 : ℤ) (N : ℤ)).card = N := by
  rw [Int.card_Icc]
  simp

/-- `G_k(N)` is a lower bound for every `N`-element set (PROVED in Lean). -/
theorem erdos_problem_201.G_ap_le_maxAPFreeSize (k : ℕ) (S : Finset ℤ) :
    G_ap k S.card ≤ maxAPFreeSize k S :=
  Nat.sInf_le ⟨S, rfl, rfl⟩

/-- `G_k(N)` is attained by some `N`-element set (PROVED in Lean). -/
theorem erdos_problem_201.exists_card_eq_G_ap (k N : ℕ) :
    ∃ S : Finset ℤ, S.card = N ∧ maxAPFreeSize k S = G_ap k N :=
  Nat.sInf_mem (s := {m : ℕ | ∃ S : Finset ℤ, S.card = N ∧ maxAPFreeSize k S = m})
    ⟨_, Finset.Icc (1 : ℤ) (N : ℤ), erdos_problem_201.card_Icc N, rfl⟩

/-- The page's trivial inequality `G_k(N) ≤ R_k(N)` (PROVED in Lean). -/
theorem erdos_problem_201.G_ap_le_R_ap (k N : ℕ) : G_ap k N ≤ R_ap k N :=
  Nat.sInf_le ⟨Finset.Icc (1 : ℤ) (N : ℤ), erdos_problem_201.card_Icc N, rfl⟩

/-- `G_3(N) ≥ 1` for `N ≥ 1`: a single point contains no 3-term progression (PROVED in Lean). -/
theorem erdos_problem_201.one_le_G_ap {N : ℕ} (hN : 1 ≤ N) : 1 ≤ G_ap 3 N := by
  obtain ⟨S, hS, hG⟩ := erdos_problem_201.exists_card_eq_G_ap 3 N
  rw [← hG]
  obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hfree : ¬HasKTermAP 3 ({x} : Finset ℤ) := by
    rintro ⟨a, d, hd, h⟩
    have h0 := h 0
    have h1 := h 1
    simp at h0 h1
    exact hd (by omega)
  have := erdos_problem_201.card_le_maxAPFreeSize (Finset.singleton_subset_iff.2 hx) hfree
  simpa using this

/-- The main statement is `(1 - ε) R_3(N) ≤ G_3(N)` for large `N` (PROVED in Lean). -/
theorem erdos_problem_201.iff_G_form :
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, S.card = N →
        ∃ T ⊆ S, ¬HasKTermAP 3 T ∧
          (1 - ε) * (R_ap 3 N : ℝ) ≤ (T.card : ℝ)) ↔
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * (R_ap 3 N : ℝ) ≤ (G_ap 3 N : ℝ) := by
  constructor
  · intro h ε hε
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨S, hS, hG⟩ := erdos_problem_201.exists_card_eq_G_ap 3 N
    obtain ⟨T, hTS, hT, hle⟩ := hN₀ N hN S hS
    have h1 : T.card ≤ G_ap 3 N := by
      rw [← hG]
      exact erdos_problem_201.card_le_maxAPFreeSize hTS hT
    exact hle.trans (by exact_mod_cast h1)
  · intro h ε hε
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨N₀, fun N hN S hS => ?_⟩
    obtain ⟨T, hTS, hT, hcard⟩ :=
      erdos_problem_201.exists_card_eq_maxAPFreeSize (k := 3) (by norm_num) S
    refine ⟨T, hTS, hT, (hN₀ N hN).trans ?_⟩
    have h1 : G_ap 3 N ≤ T.card := by
      rw [hcard, ← hS]
      exact erdos_problem_201.G_ap_le_maxAPFreeSize 3 S
    exact_mod_cast h1

/-- The main statement is the page's literal question, `R_3(N) / G_3(N) → 1` (PROVED in Lean).
The quotient is by `G_3(N) ≥ 1` for `N ≥ 1`; the value at `N = 0` (`0 / 0 = 0` in Lean) does not
affect the limit. -/
theorem erdos_problem_201.iff_limit :
    (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ S : Finset ℤ, S.card = N →
        ∃ T ⊆ S, ¬HasKTermAP 3 T ∧
          (1 - ε) * (R_ap 3 N : ℝ) ≤ (T.card : ℝ)) ↔
    Filter.Tendsto (fun N : ℕ => (R_ap 3 N : ℝ) / (G_ap 3 N : ℝ)) Filter.atTop (nhds 1) := by
  rw [erdos_problem_201.iff_G_form, Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    have hc1 : (1 : ℝ) < 1 + ε / 2 := by linarith
    have hc0 : (0 : ℝ) < 1 + ε / 2 := by linarith
    obtain ⟨N₀, hN₀⟩ := h (1 - (1 + ε / 2)⁻¹) (sub_pos.2 (inv_lt_one_of_one_lt₀ hc1))
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hG : (0 : ℝ) < (G_ap 3 N : ℝ) := by
      exact_mod_cast erdos_problem_201.one_le_G_ap hN1
    have hGR : (G_ap 3 N : ℝ) ≤ (R_ap 3 N : ℝ) := by
      exact_mod_cast erdos_problem_201.G_ap_le_R_ap 3 N
    have h1 := hN₀ N hN0
    rw [sub_sub_cancel] at h1
    have h2 : (R_ap 3 N : ℝ) ≤ (1 + ε / 2) * (G_ap 3 N : ℝ) := by
      have h3 := mul_le_mul_of_nonneg_left h1 hc0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul] at h3
    rw [Real.dist_eq, abs_lt]
    constructor
    · have h4 : (1 : ℝ) ≤ (R_ap 3 N : ℝ) / (G_ap 3 N : ℝ) := by
        rw [le_div_iff₀ hG]
        linarith
      linarith
    · have h4 : (R_ap 3 N : ℝ) / (G_ap 3 N : ℝ) ≤ 1 + ε / 2 := by
        rw [div_le_iff₀ hG]
        exact h2
      linarith
  · intro h ε hε
    obtain ⟨N₀, hN₀⟩ := h ε hε
    refine ⟨max N₀ 1, fun N hN => ?_⟩
    have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hG : (0 : ℝ) < (G_ap 3 N : ℝ) := by
      exact_mod_cast erdos_problem_201.one_le_G_ap hN1
    have hR : (0 : ℝ) ≤ (R_ap 3 N : ℝ) := Nat.cast_nonneg _
    have h1 := hN₀ N hN0
    rw [Real.dist_eq, abs_lt] at h1
    have h2 : (R_ap 3 N : ℝ) < (1 + ε) * (G_ap 3 N : ℝ) := by
      have h3 := h1.2
      rw [sub_lt_iff_lt_add] at h3
      have h4 := (div_lt_iff₀ hG).1 h3
      linarith
    by_cases hε1 : 1 ≤ ε
    · have h5 := mul_nonneg (sub_nonneg.2 hε1) hR
      linarith
    · have hε1' : 0 < 1 - ε := by linarith [not_le.1 hε1]
      have h5 := mul_lt_mul_of_pos_left h2 hε1'
      have h6 := mul_nonneg (sq_nonneg ε) hG.le
      nlinarith

/-- The page's value `R_3(5) = 4` under the input's definitions (PROVED in Lean): `{1, 2, 4, 5}`
has no 3-term progression, and `{1, …, 5}` has one. -/
theorem erdos_problem_201.R_ap_three_five : R_ap 3 5 = 4 := by
  apply le_antisymm
  · unfold R_ap maxAPFreeSize
    refine Finset.sup_le fun T hT => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    by_contra hlt
    have hTeq : T = Finset.Icc (1 : ℤ) ((5 : ℕ) : ℤ) :=
      Finset.eq_of_subset_of_card_le hT.1 (by rw [erdos_problem_201.card_Icc]; omega)
    apply hT.2
    refine ⟨1, 1, one_ne_zero, fun i => ?_⟩
    rw [hTeq, Finset.mem_Icc]
    have hi := i.isLt
    push_cast
    constructor <;> omega
  · have hfree : ¬HasKTermAP 3 ({1, 2, 4, 5} : Finset ℤ) := by
      rintro ⟨a, d, hd, h⟩
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      simp at h0 h1 h2
      omega
    have hsub : ({1, 2, 4, 5} : Finset ℤ) ⊆ Finset.Icc (1 : ℤ) ((5 : ℕ) : ℤ) := by
      intro x hx
      simp at hx
      rw [Finset.mem_Icc]
      push_cast
      omega
    have hcard : ({1, 2, 4, 5} : Finset ℤ).card = 4 := by decide
    have := erdos_problem_201.card_le_maxAPFreeSize hsub hfree
    rw [hcard] at this
    exact this

/-- Komlós, Sulyok and Szemerédi [KSS75] (SOLVED; not proved here): `R_k(N) ≪_k G_k(N)`. This is the
page's recorded partial answer to "how does `G_k(N)` relate to `R_k(N)`?". -/
theorem erdos_problem_201.variants.kss (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (R_ap k N : ℝ) ≤ C * (G_ap k N : ℝ) := by
  sorry

end
