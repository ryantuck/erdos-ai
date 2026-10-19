-- [AI - Claude Opus 5.5]: Erdős Problem 169 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Combinatorics.HalesJewett

/-!
# Erdős Problem #169

*Source:* [erdosproblems.com/169](https://www.erdosproblems.com/169) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-02-20; OEIS A005346).
[Er77c] [ErGr79] [Er80] [ErGr80]

Let $k\geq 3$ and $f(k)$ be the supremum of $\sum_{n\in A}\frac{1}{n}$ as $A$ ranges over all sets
of positive integers which do not contain a $k$-term arithmetic progression. Estimate $f(k)$.
Is $\lim_{k\to \infty}\frac{f(k)}{\log W(k)}=\infty$ where $W(k)$ is the van der Waerden number?

Remarks recorded on the page: Berlekamp [Be68] proved $f(k)\ge\frac{\log2}{2}k$. Gerver [Ge77]
proved $f(k)\ge(1-o(1))k\log k$. It is trivial that $\frac{f(k)}{\log W(k)}\ge\frac12$, but
improving the right-hand side to any constant $>1/2$ is open. Gerver also proved (see the comments
for an alternative argument of Tao) that [3] is equivalent to $f(k)$ being finite for all $k$. The
current record for $f(3)$ is $f(3)\ge3.00849$, due to Wróblewski [Wr84]. Walker [Wa25] proved
$f(4)\ge4.43975$, and showed that it suffices to consider Kempner sets.

## Encoding notes

* `f(k)` is not defined. For sets of positive integers the reciprocal sum of an infinite set is the
  supremum of those of its finite subsets, which are AP-free when the set is; so $f(k)$ is the
  supremum over finite AP-free sets, and "$f(k)/\log W(k)\to\infty$" is the main theorem: for
  every `C > 0`, for all large `k`, some finite `k`-AP-free set of positive integers has reciprocal
  sum `> C · log W(k)`. This is the "yes" direction of the open question; "estimate $f(k)$" has no
  formal target.
* `vanDerWaerdenNumber k` is the least `N` such that every `2`-colouring of `{0, …, N - 1}` has a
  monochromatic `k`-term progression; this is $W(k)$ (colouring `{1, …, N}` instead is a shift).
  Values (PROVED): `W 0 = 1`, `W 1 = 1`, `W 2 = 3`.
* The input proved van der Waerden's theorem `vdw_exists` with `sorry`, so the definition of `W`
  depended on `sorryAx`. v2 proves it from Mathlib's Hales–Jewett theorem, with the statement
  unchanged.
* The page's trivial bound $f(k)\ge\frac12\log W(k)$ is PROVED in Lean (`variants.trivial_half`).

## References

From the site's `/latex/169` bibliography:
* [Be68] Berlekamp, E. R., _A construction for partitions which avoid long arithmetic
  progressions_. Canad. Math. Bull. (1968), 409–414.
* [Ge77] Gerver, J. L., _The sum of the reciprocals of a set of integers with no arithmetic
  progression of $k$ terms_. Proc. Amer. Math. Soc. (1977), 211–214.
* [Wr84] Wróblewski, J., _A nonaveraging set of integers with a large sum of reciprocals_. Math.
  Comp. (1984), 261–262.
* [Wa25] Walker, A., _Integer sets of large harmonic sum which avoid long arithmetic progressions_.
  arXiv:2203.06045 (2025).

Erdős's sources:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72. (Site `/latex/460` and others.)
* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89–115. (Site `/latex/425`, `/latex/687`.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/169.lean` (Opus 5.5 review, `opus-5-5-review/169.md`).
-/

open Finset BigOperators Real

/-- A finset of natural numbers is k-AP-free if it contains no arithmetic
progression of length k with positive common difference. -/
def IsAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- The van der Waerden property: every 2-coloring of {0, ..., N-1} contains
a monochromatic k-term arithmetic progression. -/
def VDWProperty (k N : ℕ) : Prop :=
  ∀ f : ℕ → Bool, ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ∀ i : ℕ, i < k → f (a + i * d) = f a

/-- Van der Waerden's theorem guarantees the existence of W(k) for all k.
(PROVED in Lean; the input had `sorry`. Mathlib's Hales–Jewett theorem gives a monochromatic
combinatorial line in `ι → Fin k`; the sum of coordinates maps it to a `k`-term progression with
common difference the number of moving coordinates, inside `{0, …, |ι|(k - 1)}`.) -/
lemma vdw_exists (k : ℕ) : ∃ N, VDWProperty k N := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, fun f => ⟨0, 1, Nat.one_pos, by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  refine ⟨Fintype.card ι * (k - 1) + 1, fun f => ?_⟩
  obtain ⟨l, c, hl⟩ := hι fun v => f (∑ i, ((v i : Fin k) : ℕ))
  let s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none)
  let b : ℕ := ∑ i ∈ sᶜ, ((l.idxFun i).map (fun m : Fin k => (m : ℕ))).getD 0
  have hsum : ∀ x : Fin k, ∑ i, ((l x i : Fin k) : ℕ) = b + s.card * (x : ℕ) := by
    intro x
    have e1 : ∑ i ∈ sᶜ, ((l x i : Fin k) : ℕ) = b := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_compl, Finset.mem_filter] at hi
      have hi' : l.idxFun i ≠ none := fun h => hi ⟨Finset.mem_univ _, h⟩
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi'
      rw [Combinatorics.Line.apply_some hy.symm, ← hy]
      rfl
    have e2 : ∑ i ∈ s, ((l x i : Fin k) : ℕ) = s.card * (x : ℕ) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_filter] at hi
      rw [Combinatorics.Line.apply_none _ _ _ hi.2]
    rw [← Finset.sum_add_sum_compl s, e1, e2, add_comm]
  have hd : 0 < s.card := Finset.card_pos.mpr
    ⟨l.proper.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  refine ⟨b, s.card, hd, ?_, ?_⟩
  · have h1 := hsum ⟨k - 1, by omega⟩
    have hle : ∑ i, ((l ⟨k - 1, by omega⟩ i : Fin k) : ℕ) ≤ Fintype.card ι * (k - 1) := by
      calc ∑ i, ((l ⟨k - 1, by omega⟩ i : Fin k) : ℕ) ≤ ∑ _i : ι, (k - 1) :=
            Finset.sum_le_sum (fun i _ => by have := (l ⟨k - 1, by omega⟩ i).isLt; omega)
        _ = Fintype.card ι * (k - 1) := by simp
    rw [h1] at hle
    have : (k - 1) * s.card = s.card * (k - 1) := Nat.mul_comm _ _
    dsimp only at hle
    omega
  · intro i hi
    have h1 := hl ⟨i, hi⟩
    have h0 := hl ⟨0, hk⟩
    simp only at h1 h0
    rw [hsum] at h1 h0
    simp only [mul_zero, add_zero] at h1 h0
    rw [Nat.mul_comm i, h1, h0]

open Classical in
/-- The van der Waerden number W(k): the smallest N such that any 2-coloring
of {0, ..., N-1} contains a monochromatic k-term AP. -/
noncomputable def vanDerWaerdenNumber (k : ℕ) : ℕ :=
  Nat.find (vdw_exists k)

/--
Erdős Problem #169:
Let k ≥ 3 and f(k) be the supremum of ∑_{n ∈ A} 1/n over all sets A of
positive integers containing no k-term arithmetic progression.

Is lim_{k → ∞} f(k) / log W(k) = ∞, where W(k) is the van der Waerden number?

This is formalized as: for every constant C > 0, for all sufficiently large k,
there exists a finite AP-free set A of positive integers whose reciprocal sum
exceeds C · log W(k). (Status: OPEN.)
-/
theorem erdos_problem_169_conjecture :
    ∀ C : ℝ, 0 < C → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
        C * Real.log (↑(vanDerWaerdenNumber k) : ℝ) <
          ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) :=
  sorry


/-- `W(0) = 1` with this definition: a `0`-term progression needs only a start `a < N`
(PROVED in Lean). -/
theorem erdos_problem_169.vanDerWaerdenNumber_zero : vanDerWaerdenNumber 0 = 1 := by
  classical
  unfold vanDerWaerdenNumber
  rw [Nat.find_eq_iff]
  refine ⟨fun f => ⟨0, 1, Nat.one_pos, by simp, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, ?_⟩
  intro n hn h
  obtain ⟨a, d, -, had, -⟩ := h (fun _ => true)
  omega

/-- `W(1) = 1` (PROVED in Lean). -/
theorem erdos_problem_169.vanDerWaerdenNumber_one : vanDerWaerdenNumber 1 = 1 := by
  classical
  unfold vanDerWaerdenNumber
  rw [Nat.find_eq_iff]
  refine ⟨fun f => ⟨0, 1, Nat.one_pos, by simp, fun i hi => by
    have : i = 0 := by omega
    subst this; simp⟩, ?_⟩
  intro n hn h
  obtain ⟨a, d, -, had, -⟩ := h (fun _ => true)
  omega

/-- `W(2) = 3`: among `0, 1, 2` two have the same colour, and the colouring `0 ↦ true`,
`1 ↦ false` has no monochromatic pair in `{0, 1}` (PROVED in Lean). -/
theorem erdos_problem_169.vanDerWaerdenNumber_two : vanDerWaerdenNumber 2 = 3 := by
  classical
  unfold vanDerWaerdenNumber
  rw [Nat.find_eq_iff]
  constructor
  · intro f
    have key : ∀ a d : ℕ, f (a + d) = f a → (0 < d ∧ a + (2 - 1) * d < 3) →
        ∃ a d : ℕ, 0 < d ∧ a + (2 - 1) * d < 3 ∧ ∀ i : ℕ, i < 2 → f (a + i * d) = f a := by
      intro a d h hd
      refine ⟨a, d, hd.1, hd.2, fun i hi => ?_⟩
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · simp
      · simpa using h
    by_cases h01 : f (0 + 1) = f 0
    · exact key 0 1 h01 ⟨Nat.one_pos, by norm_num⟩
    by_cases h12 : f (1 + 1) = f 1
    · exact key 1 1 h12 ⟨Nat.one_pos, by norm_num⟩
    · apply key 0 2 _ ⟨by norm_num, by norm_num⟩
      revert h01 h12
      cases f 0 <;> cases f 1 <;> cases f (0 + 2) <;> simp_all
  · intro n hn h
    obtain ⟨a, d, hd, had, hf⟩ := h (fun m => decide (m = 0))
    have := hf 1 (by norm_num)
    have ha : a = 0 := by omega
    have hd1 : d = 1 := by omega
    subst ha hd1
    simp at this

/-- `log (M + 1) ≤ ∑_{n=1}^{M} 1/n` (PROVED in Lean, from `log x ≤ x - 1`). -/
theorem erdos_problem_169.log_succ_le_sum (M : ℕ) :
    Real.log ((M : ℝ) + 1) ≤ ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have hstep : Real.log ((M : ℝ) + 1 + 1) - Real.log ((M : ℝ) + 1) ≤ 1 / ((M : ℝ) + 1) := by
      rw [← Real.log_div (by positivity) hM.ne']
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((M : ℝ) + 1 + 1) / ((M : ℝ) + 1) by positivity)
      have e : ((M : ℝ) + 1 + 1) / ((M : ℝ) + 1) - 1 = 1 / ((M : ℝ) + 1) := by
        field_simp; ring
      linarith
    push_cast
    linarith

/-- The page's trivial bound $f(k)\ge\frac12\log W(k)$ (PROVED in Lean): a colouring of
`{1, …, W(k) - 1}` without monochromatic `k`-term progressions splits it into two `k`-AP-free sets,
one of which carries half of $\sum_{n<W(k)}1/n\ge\log W(k)$. -/
theorem erdos_problem_169.variants.trivial_half (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
      (1 / 2 : ℝ) * Real.log (vanDerWaerdenNumber k : ℝ) ≤ ∑ n ∈ A, (1 : ℝ) / (n : ℝ) := by
  classical
  set W := vanDerWaerdenNumber k with hW
  have hWpos : 1 ≤ W := by
    rw [hW]; unfold vanDerWaerdenNumber
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    have := Nat.find_spec (vdw_exists k)
    rw [h0] at this
    obtain ⟨a, d, -, had, -⟩ := this (fun _ => true)
    omega
  -- a colouring of {0, …, W - 2} with no monochromatic k-term progression
  have hnot : ¬ VDWProperty k (W - 1) := by
    rw [hW]; unfold vanDerWaerdenNumber
    exact Nat.find_min (vdw_exists k) (by unfold vanDerWaerdenNumber at hW; omega)
  unfold VDWProperty at hnot
  push_neg at hnot
  obtain ⟨f, hf⟩ := hnot
  let A : Bool → Finset ℕ := fun c => (Finset.Icc 1 (W - 1)).filter (fun n => f (n - 1) = c)
  have hApos : ∀ c, ∀ n ∈ A c, 0 < n := by
    intro c n hn
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hn
    omega
  have hAfree : ∀ c, IsAPFree k (A c) := by
    intro c ⟨a', d, hd, hmem⟩
    have h0 := hmem 0 (by omega)
    simp only [A, Finset.mem_filter, Finset.mem_Icc, zero_mul, add_zero] at h0
    have hlast := hmem (k - 1) (by omega)
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hlast
    obtain ⟨i, hi, hne⟩ := hf (a' - 1) d hd (by omega)
    apply hne
    have hi' := hmem i hi
    simp only [A, Finset.mem_filter, Finset.mem_Icc] at hi'
    have e1 : a' - 1 + i * d = a' + i * d - 1 := by omega
    rw [e1, hi'.2, h0.2]
  have hsplit : ∑ n ∈ A true, (1 : ℝ) / (n : ℝ) + ∑ n ∈ A false, (1 : ℝ) / (n : ℝ) =
      ∑ n ∈ Finset.Icc 1 (W - 1), (1 : ℝ) / (n : ℝ) := by
    have := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (W - 1))
      (fun n => f (n - 1) = true) (fun n => (1 : ℝ) / (n : ℝ))
    simpa [A] using this
  have hlog : Real.log (W : ℝ) ≤ ∑ n ∈ Finset.Icc 1 (W - 1), (1 : ℝ) / (n : ℝ) := by
    have := erdos_problem_169.log_succ_le_sum (W - 1)
    have e : ((W - 1 : ℕ) : ℝ) + 1 = (W : ℝ) := by
      rw [Nat.cast_sub hWpos]; ring
    rwa [e] at this
  by_cases hc : (1 / 2 : ℝ) * Real.log (W : ℝ) ≤ ∑ n ∈ A true, (1 : ℝ) / (n : ℝ)
  · exact ⟨A true, hApos true, hAfree true, hc⟩
  · exact ⟨A false, hApos false, hAfree false, by linarith⟩

/-- Gerver [Ge77] (SOLVED; not proved here): $f(k)\ge(1-o(1))k\log k$. -/
theorem erdos_problem_169.variants.gerver :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
        (1 - ε) * (k : ℝ) * Real.log (k : ℝ) < ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) :=
  sorry

/-- Wróblewski [Wr84] (SOLVED; not proved here): $f(3)\ge3.00849$. -/
theorem erdos_problem_169.variants.wroblewski :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree 3 A ∧
        (3.00849 : ℝ) - ε < ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) :=
  sorry

/-- Walker [Wa25] (SOLVED; not proved here): $f(4)\ge4.43975$. -/
theorem erdos_problem_169.variants.walker :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree 4 A ∧
        (4.43975 : ℝ) - ε < ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) :=
  sorry

/-- Gerver [Ge77] (SOLVED; not proved here): Problem [3] (a set of positive integers with divergent
reciprocal sum has arbitrarily long progressions) is equivalent to $f(k)<\infty$ for every `k`. -/
theorem erdos_problem_169.variants.problem3_equiv :
    (∀ k : ℕ, ∃ B : ℝ, ∀ A : Finset ℕ, (∀ n ∈ A, 0 < n) → IsAPFree k A →
      ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) ≤ B) ↔
    (∀ A : Set ℕ, (∀ n ∈ A, 0 < n) →
      (¬ Summable fun a : A => (1 : ℝ) / ((a : ℕ) : ℝ)) →
      ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A) :=
  sorry
