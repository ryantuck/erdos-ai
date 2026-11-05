-- [AI - Claude Opus 5.5]: Erdős Problem 187 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Real

noncomputable section

/-!
# Erdős Problem #187

*Source:* [erdosproblems.com/187](https://www.erdosproblems.com/187) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-02-20; page edited
01 January 2026). [Er73] [ErGr79] [ErGr80, p.17]

Find the best function $f(d)$ such that, in any 2-colouring of the integers, at least one colour
class contains an arithmetic progression with common difference $d$ of length $f(d)$ for infinitely
many $d$.

Remarks recorded on the page (abridged): originally asked by Cohen. Erdős observed that colouring
according to whether $\{\sqrt{2}n\}<1/2$ or not implies $f(d)\ll d$ (using $\|\sqrt2q\|\gg1/q$).
Beck [Be80] improved this using the probabilistic method, constructing a colouring that shows
$f(d)\leq(1+o(1))\log_2 d$. Van der Waerden's theorem implies $f(d)\to\infty$ is necessary.

## Encoding notes

* The page asks to *find* the best function and records only the bounds above: $f\to\infty$
  (van der Waerden) and $f(d)\le(1+o(1))\log_2d$ (Beck). It records no conjecture for the answer.
* The first pass asserted $f(d)\gg\log d$, the lower half of the natural candidate $\Theta(\log d)$.
  That guess is not on the page; it is kept as `variants.first_pass_guess` (OPEN, editorial).
* v2's main theorem is the editorial reading "the best function has order $\log d$": the guess
  together with a matching upper bound. Its upper half follows from Beck's theorem, so given Beck it
  is equivalent to the guess (`variants.main_of_guess_and_beck`, PROVED in Lean).
* The known lower bound is PROVED in Lean from Mathlib's Hales–Jewett theorem (`variants.vdw`):
  every 2-colouring has, for every `k`, monochromatic `k`-term progressions with arbitrarily large
  common difference.
* `hasMonoAP χ 0 k` holds for every `k` (a constant "progression"), so the requirement `N < d` with
  `d` large is essential (`hasMonoAP_zero`, PROVED).

## References

From the site's `/latex/187` bibliography:
* [Be80] Beck, József, _A remark concerning arithmetic progressions_. J. Combin. Theory Ser. A
  (1980), 376–379.

Erdős's sources:
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138. (Site `/latex/783` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/187.lean` (Opus 5.5 review, `opus-5-5-review/187.md`).
-/

/-- A 2-colouring χ : ℤ → Bool has a monochromatic arithmetic progression of
    length k with common difference d: there exist a starting point a ∈ ℤ and
    a colour c such that χ(a + i·d) = c for all 0 ≤ i < k. -/
def hasMonoAP (χ : ℤ → Bool) (d : ℕ) (k : ℕ) : Prop :=
  ∃ a : ℤ, ∃ c : Bool, ∀ i : ℕ, i < k → χ (a + ↑i * ↑d) = c

/--
Erdős Problem #187 [Er73, ErGr79, ErGr80], editorial reading (OPEN): the best function has order
$\log d$. There are constants $c, C>0$ such that every 2-colouring of $\mathbb Z$ has, for infinitely
many $d$, a monochromatic progression with common difference $d$ and length at least $c\log d$, and
some 2-colouring has none of length above $C\log d$ for large $d$.

The page records only $f\to\infty$ and Beck's upper bound; this reading is not on the page. Its upper
half follows from Beck's theorem [Be80] (`variants.main_of_guess_and_beck`).
-/
theorem erdos_problem_187 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ χ : ℤ → Bool, ∀ N : ℕ, ∃ d : ℕ, N < d ∧
        ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ hasMonoAP χ d k) ∧
      (∃ χ : ℤ → Bool, ∀ᶠ d : ℕ in Filter.atTop, ∀ k : ℕ, hasMonoAP χ d k →
        (k : ℝ) ≤ C * Real.log ↑d) :=
  sorry

/-- The first pass's statement (OPEN; a guess not recorded on the page): $f(d)\gg\log d$. -/
theorem erdos_problem_187.variants.first_pass_guess :
    ∃ c : ℝ, 0 < c ∧
    ∀ χ : ℤ → Bool,
    ∀ N : ℕ, ∃ d : ℕ, N < d ∧
      ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ hasMonoAP χ d k :=
  sorry

/-- Beck's theorem [Be80] (SOLVED; not proved here): some 2-colouring has, for every `ε > 0` and all
large `d`, no monochromatic progression with common difference `d` longer than
$(1+\varepsilon)\log_2 d$. -/
theorem erdos_problem_187.variants.beck :
    ∃ χ : ℤ → Bool, ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in Filter.atTop, ∀ k : ℕ, hasMonoAP χ d k →
      (k : ℝ) ≤ (1 + ε) * Real.logb 2 d :=
  sorry

/-- Erdős's observation (SOLVED; not proved here): colouring by whether $\{\sqrt2n\}<1/2$ gives
$f(d)\ll d$. -/
theorem erdos_problem_187.variants.erdos_sqrt_two :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 1 ≤ d → ∀ k : ℕ,
      hasMonoAP (fun n : ℤ => decide (Int.fract (Real.sqrt 2 * n) < 1 / 2)) d k →
      (k : ℝ) ≤ C * d :=
  sorry

/-- The first pass's guess and Beck's theorem together give the main theorem (PROVED in Lean). -/
theorem erdos_problem_187.variants.main_of_guess_and_beck
    (hg : ∃ c : ℝ, 0 < c ∧ ∀ χ : ℤ → Bool, ∀ N : ℕ, ∃ d : ℕ, N < d ∧
      ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ hasMonoAP χ d k)
    (hb : ∃ χ : ℤ → Bool, ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in Filter.atTop, ∀ k : ℕ, hasMonoAP χ d k →
      (k : ℝ) ≤ (1 + ε) * Real.logb 2 d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ χ : ℤ → Bool, ∀ N : ℕ, ∃ d : ℕ, N < d ∧
        ∃ k : ℕ, c * Real.log ↑d ≤ ↑k ∧ hasMonoAP χ d k) ∧
      (∃ χ : ℤ → Bool, ∀ᶠ d : ℕ in Filter.atTop, ∀ k : ℕ, hasMonoAP χ d k →
        (k : ℝ) ≤ C * Real.log ↑d) := by
  obtain ⟨c, hc, hg⟩ := hg
  obtain ⟨χ, hχ⟩ := hb
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨c, 2 / Real.log 2, hc, by positivity, hg, χ, ?_⟩
  filter_upwards [hχ 1 one_pos] with d hd k hk
  have h := hd k hk
  rw [Real.logb] at h
  calc (k : ℝ) ≤ (1 + 1) * (Real.log d / Real.log 2) := h
    _ = 2 / Real.log 2 * Real.log d := by ring

/-- `hasMonoAP χ 0 k` holds for every `k`: with common difference `0` every "progression" is constant
(PROVED in Lean). So the common difference must be taken large, as the statements do. -/
theorem erdos_problem_187.hasMonoAP_zero (χ : ℤ → Bool) (k : ℕ) : hasMonoAP χ 0 k :=
  ⟨0, χ 0, fun i _ => by simp⟩

/-- Van der Waerden's theorem with large common difference (PROVED in Lean, from Mathlib's
Hales–Jewett theorem): in every 2-colouring of $\mathbb Z$, for every `k` and `N` there is a
monochromatic `k`-term progression whose common difference exceeds `N`. This is the page's
"$f(d)\to\infty$ is necessary". -/
theorem erdos_problem_187.variants.vdw (χ : ℤ → Bool) (k N : ℕ) :
    ∃ d : ℕ, N < d ∧ hasMonoAP χ d k := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨N + 1, Nat.lt_succ_self N, 0, true, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  obtain ⟨l, c, hl⟩ := hι fun v => χ (((N + 1) * ∑ i, ((v i : Fin k) : ℕ) : ℕ) : ℤ)
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
  refine ⟨(N + 1) * s.card, ?_, (((N + 1) * b : ℕ) : ℤ), c, fun i hi => ?_⟩
  · calc N < N + 1 := Nat.lt_succ_self N
      _ = (N + 1) * 1 := (mul_one _).symm
      _ ≤ (N + 1) * s.card := Nat.mul_le_mul_left _ hd
  · have h1 := hl ⟨i, hi⟩
    simp only at h1
    rw [hsum] at h1
    rw [← h1]
    congr 1
    push_cast
    ring

end
