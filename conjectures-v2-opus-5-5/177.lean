-- [AI - Claude Opus 5.5]: Erdős Problem 177 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Combinatorics.HalesJewett

/-!
# Erdős Problem #177

*Source:* [erdosproblems.com/177](https://www.erdosproblems.com/177) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-02-20). [Er73] [ErGr79] [ErGr80]

Find the smallest $h(d)$ such that the following holds. There exists a function
$f:\mathbb{N}\to\{-1,1\}$ such that, for every $d\geq 1$,
$\max_{P_d}\left\lvert \sum_{n\in P_d}f(n)\right\rvert\leq h(d)$, where $P_d$ ranges over all
finite arithmetic progressions with common difference $d$.

Remarks recorded on the page: Cantor, Erdős, Schreiber, and Straus [Er66] proved that $h(d)\ll d!$
is possible. Van der Waerden's theorem implies that $h(d)\to\infty$. Beck [Be17] has shown that
$h(d)\leq d^{8+\epsilon}$ is possible for every $\epsilon>0$. Roth's famous discrepancy lower bound
[Ro64] implies that $h(d)\gg d^{1/2}$.

## Encoding notes

* The question asks for the optimal growth of `h`; no answer is conjectured, so it has no formal
  target. `Bounds f h` below says that `f` has discrepancy at most `h d` along every progression of
  difference `d`; the page's results are stated with it.
* **The input's two theorems are false as stated** (both refutations PROVED in Lean):
  - `erdos_problem_177_lower` asked for discrepancy `≥ c √d` along **every** difference `d`. But
    `f n = (-1) ^ (n / d₀)` has discrepancy at most `1` along difference `d₀`
    (`variants.first_pass_lower_false`). Roth's bound concerns some differences, not all.
  - `erdos_problem_177_upper` asked for discrepancy `≤ d ^ (8 + ε)` for **every** `d ≥ 1`. At `d = 1`
    this forces `f` to alternate, and then the sums along difference `2` are unbounded
    (`variants.first_pass_upper_false`). Beck's bound is asymptotic (here: up to a constant).
  v2 states the two results in corrected forms (`variants.roth`, `variants.beck`; not proved).
* Van der Waerden's theorem gives arbitrarily long monochromatic progressions, so no `±1` sequence
  has bounded discrepancy (`variants.vdw_unbounded`, `variants.vdw_h_unbounded`, PROVED in Lean from
  Mathlib's Hales–Jewett theorem).

## References

From the site's `/latex/177` bibliography:
* [Er66] Erdős, P., _Remarks on number theory. V. Extremal problems in number theory. II_. Mat.
  Lapok (1966), 135–155.
* [Ro64] Roth, K. F., _Remark concerning integer sequences_. Acta Arith. (1964), 257–260.
* [Be17] Beck, J., _A discrepancy problem: balancing infinite dimensional vectors_. Number
  theory–Diophantine problems, uniform distribution and applications (2017), 61–82.

Erdős's sources:
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973),
  117–138. (Site `/latex/783` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/177.lean` (Opus 5.5 review, `opus-5-5-review/177.md`).
The input's two theorems are replaced by proofs of their negations.
-/

open Finset BigOperators Real

noncomputable section

/-- `Bounds f h`: along every progression `a, a + d, …, a + (k - 1) d` with `d ≥ 1`, the sum of `f` has
absolute value at most `h d` (review addition). -/
def erdos_problem_177.Bounds (f : ℕ → ℤ) (h : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ a k : ℕ, |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| ≤ h d

/-- Partial sums of `(-1)^i` are `k % 2` (PROVED in Lean). -/
theorem erdos_problem_177.sum_neg_one_pow (k : ℕ) : ∑ i ∈ range k, (-1 : ℤ) ^ i = (k % 2 : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_one_pow, Nat.even_iff.mp h, Nat.succ_mod_two_eq_one_iff.mpr (Nat.even_iff.mp h)]
      norm_num
    · rw [h.neg_one_pow, Nat.odd_iff.mp h, Nat.succ_mod_two_eq_zero_iff.mpr (Nat.odd_iff.mp h)]
      norm_num

/-- The input's lower bound (Roth, as first formalized) is false (PROVED in Lean): for `d₀ > 1/c²`,
`f n = (-1) ^ (n / d₀)` alternates along every progression of difference `d₀`, so all those sums
are `0` or `±1`. -/
theorem erdos_problem_177.variants.first_pass_lower_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ f : ℕ → ℤ,
      (∀ n, f n = 1 ∨ f n = -1) →
      ∀ d : ℕ, 0 < d →
      ∃ a k : ℕ, 0 < k ∧
        c * Real.sqrt (↑d) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| := by
  rintro ⟨c, hc, h⟩
  obtain ⟨d, hd⟩ := exists_nat_gt (1 / c ^ 2)
  have hdpos : 0 < d := by
    have : (0 : ℝ) < 1 / c ^ 2 := by positivity
    exact_mod_cast this.trans hd
  obtain ⟨a, k, -, hk⟩ := h (fun n => (-1) ^ (n / d))
    (fun n => by rcases neg_one_pow_eq_or ℤ (n / d) with h | h <;> simp [h]) d hdpos
  have hsum : ∑ i ∈ range k, (-1 : ℤ) ^ ((a + i * d) / d) = (-1) ^ (a / d) * ((k % 2 : ℕ) : ℤ) := by
    rw [← erdos_problem_177.sum_neg_one_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_mul_div_right _ _ hdpos, pow_add]
  have habsZ : |∑ i ∈ range k, (-1 : ℤ) ^ ((a + i * d) / d)| ≤ 1 := by
    rw [hsum, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    have : (k % 2 : ℕ) ≤ 1 := by omega
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this
  have habs : |(↑(∑ i ∈ range k, (-1 : ℤ) ^ ((a + i * d) / d)) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast habsZ
  have hsq : 1 < c * Real.sqrt d := by
    have h1 : 1 / c ^ 2 < (d : ℝ) := hd
    have h2 : 1 < c ^ 2 * d := by
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
    have h3 : c * Real.sqrt d = Real.sqrt (c ^ 2 * d) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
    rw [h3, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) h2
  linarith

/-- The input's upper bound (Beck, as first formalized) is false (PROVED in Lean): at `d = 1` the
bound `1 ^ (8 + ε) = 1` forces `f (n + 1) = - f n`, and then `f` is constant along difference `2`. -/
theorem erdos_problem_177.variants.first_pass_upper_false :
    ¬ ∀ ε : ℝ, 0 < ε →
      ∃ f : ℕ → ℤ,
      (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ d : ℕ, 0 < d → ∀ a k : ℕ, 0 < k →
        |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| ≤ (↑d : ℝ) ^ ((8 : ℝ) + ε) := by
  intro h
  obtain ⟨f, hf, hb⟩ := h 1 one_pos
  -- difference 1: consecutive values alternate
  have halt : ∀ n, f (n + 1) = - f n := by
    intro n
    have := hb 1 one_pos n 2 (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, add_zero,
      one_mul, Nat.cast_one, Real.one_rpow] at this
    rcases hf n with h1 | h1 <;> rcases hf (n + 1) with h2 | h2
    · exfalso; rw [h1, h2] at this; norm_num at this
    · simp [h1, h2]
    · simp [h1, h2]
    · exfalso; rw [h1, h2] at this; norm_num at this
  have hper : ∀ i, f (0 + i * 2) = f 0 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show 0 + (i + 1) * 2 = (0 + i * 2) + 1 + 1 by ring, halt, halt, neg_neg, ih]
  obtain ⟨K, hK⟩ := exists_nat_gt ((2 : ℝ) ^ ((8 : ℝ) + 1))
  have := hb 2 (by norm_num) 0 (K + 1) (by omega)
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at this
  have hf0 : |(f 0 : ℝ)| = 1 := by rcases hf 0 with h | h <;> simp [h]
  push_cast at this
  rw [abs_mul, hf0, mul_one, abs_of_nonneg (by positivity)] at this
  linarith

/-- Van der Waerden's theorem for `±1` sequences (PROVED in Lean, from the Hales–Jewett theorem
in Mathlib): for every `k` some `k`-term progression has `|∑| = k`. -/
theorem erdos_problem_177.variants.vdw_unbounded (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1) (k : ℕ) :
    ∃ a d : ℕ, 0 < d ∧ (k : ℝ) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, 1, one_pos, by simp⟩
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  obtain ⟨l, c, hl⟩ := hι fun v => decide (f (∑ i, ((v i : Fin k) : ℕ)) = 1)
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
  -- all terms equal the first
  have hconst : ∀ i ∈ range k, f (b + i * s.card) = f b := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 := hl ⟨i, hi⟩
    have h0 := hl ⟨0, hk⟩
    simp only at h1 h0
    rw [hsum] at h1 h0
    simp only [mul_zero, add_zero] at h1 h0
    rw [Nat.mul_comm i]
    have : decide (f (b + s.card * i) = 1) = decide (f b = 1) := h1.trans h0.symm
    rcases hf (b + s.card * i) with ha | ha <;> rcases hf b with hb | hb <;> simp_all
  refine ⟨b, s.card, hd, ?_⟩
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfb : |(f b : ℝ)| = 1 := by rcases hf b with h | h <;> simp [h]
  push_cast
  rw [abs_mul, hfb, mul_one, abs_of_nonneg (by positivity)]

/-- Hence no admissible `h` is bounded: the page's "$h(d)\to\infty$" in the form "unbounded"
(PROVED in Lean). -/
theorem erdos_problem_177.variants.vdw_h_unbounded (f : ℕ → ℤ) (hf : ∀ n, f n = 1 ∨ f n = -1)
    (h : ℕ → ℝ) (hb : erdos_problem_177.Bounds f h) (M : ℝ) :
    ∃ d : ℕ, 0 < d ∧ M ≤ h d := by
  obtain ⟨a, d, hd, hk⟩ := erdos_problem_177.variants.vdw_unbounded f hf ⌈M⌉₊
  exact ⟨d, hd, (Nat.le_ceil M).trans (hk.trans (hb d hd a ⌈M⌉₊))⟩

/-- Roth [Ro64], as the page uses it (SOLVED; not proved here; the precise form derived from
[Ro64] was not checked): an admissible `h` satisfies `h d ≥ c √d` for infinitely many `d`. -/
theorem erdos_problem_177.variants.roth :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) →
      ∀ h : ℕ → ℝ, erdos_problem_177.Bounds f h →
        ∀ D : ℕ, ∃ d : ℕ, D ≤ d ∧ 0 < d ∧ c * Real.sqrt d ≤ h d :=
  sorry

/-- Beck [Be17] (SOLVED; not proved here): for every `ε > 0` some `±1` sequence has
`h(d) ≪ d ^ (8 + ε)`, stated with a constant `C`. -/
theorem erdos_problem_177.variants.beck :
    ∀ ε : ℝ, 0 < ε → ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∃ C : ℝ, erdos_problem_177.Bounds f (fun d => C * (d : ℝ) ^ ((8 : ℝ) + ε)) :=
  sorry

/-- Cantor, Erdős, Schreiber and Straus [Er66] (SOLVED; not proved here): `h(d) ≪ d!` is
possible. -/
theorem erdos_problem_177.variants.cess :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∃ C : ℝ, erdos_problem_177.Bounds f (fun d => C * (d.factorial : ℝ)) :=
  sorry

end
