-- [AI - Claude Opus 5.5]: Erdős Problem 188 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #188

*Source:* [erdosproblems.com/188](https://www.erdosproblems.com/188) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05; page edited
14 October 2025). [ErGr79] [ErGr80]

What is the smallest $k$ such that $\mathbb{R}^2$ can be red/blue coloured with no pair of red
points unit distance apart, and no $k$-term arithmetic progression of blue points with distance
$1$?

Remarks recorded on the page (abridged): Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus
[EGMRSS75] proved $k\geq 5$. Tsaturian [Ts17] improved this to $k\geq 6$. Erdős and Graham claim
that $k\leq 10000000$ ('more or less'), but give no proof. Erdős and Graham asked this with just
any $k$-term arithmetic progression in blue (not necessarily with distance $1$), but Alon has
pointed out that in fact no such $k$ exists: in any red/blue colouring of the integer points on a
line either there are two red points distance $1$ apart, or else the set of blue points and the
same set shifted by $1$ cover all integers, and hence by van der Waerden's theorem there are
arbitrarily long blue arithmetic progressions. It seems most likely, from context, that Erdős and
Graham intended to restrict the blue arithmetic progression to have distance $1$.

## Encoding notes

* The question asks for a value. The theorem asserts that some admissible `k` exists, i.e. that
  the smallest `k` is defined; this is Erdős and Graham's unproved claim (the page says they give
  no proof). The value itself (known to be at least `6`) has no formal target here.
* Red is `true`. A blue progression with distance `1` is `p, p + v, …, p + (k-1)v` with `‖v‖ = 1`.
* Small cases: `k = 1` is impossible (every point would have to be red) (`variants.not_one`,
  PROVED in Lean). Alon's remark is PROVED in Lean (`variants.alon`, using van der Waerden's
  theorem from Mathlib's Hales–Jewett theorem): without the distance-`1` restriction no `k` works,
  so the restriction in the statement is essential.

## References

No `/latex/188` fetch is in the session logs; the entries below are from upstream
`formal-conjectures` (`2befc3a`) and are **DEFERRED** as site entries.
* [EGMRSS75] Erdős, P., Graham, R. L., Montgomery, P., Rothschild, B. L., Spencer, J. and
  Straus, E. G., _Euclidean Ramsey theorems. II_ (1975), 529–557.
* [Ts17] Tsaturian, Sergei, _A Euclidean Ramsey result in the plane_. Electron. J. Combin.
  (2017), Paper No. 4.35, 9.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171.)

*Provenance:* second pass of `conjectures/188.lean` (Opus 5.5 review, `opus-5-5-review/188.md`).
-/

/--
Erdős Problem #188 [ErGr79, ErGr80]:

What is the smallest k such that ℝ² can be red/blue coloured with no pair
of red points unit distance apart, and no k-term arithmetic progression of
blue points with distance 1?

An arithmetic progression of blue points with distance 1 means k points of
the form p, p + v, p + 2v, …, p + (k−1)v where ‖v‖ = 1, all coloured blue.

Known bounds: k ≥ 6 (Tsaturian, 2017). Erdős and Graham claim k ≤ 10⁷
('more or less'), but give no proof.

The statement asserts that some admissible k exists, so that the smallest one is defined (OPEN:
Erdős and Graham's claim, unproved per the page).
-/
theorem erdos_problem_188 :
    ∃ k : ℕ, ∃ f : EuclideanSpace ℝ (Fin 2) → Bool,
      -- No two red (true) points at unit distance
      (∀ x y : EuclideanSpace ℝ (Fin 2),
        f x = true → f y = true → ‖x - y‖ = 1 → False) ∧
      -- No k-term arithmetic progression of blue (false) points with step distance 1
      (∀ (p v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
        ¬∀ i : Fin k, f (p + (i : ℕ) • v) = false) :=
  sorry

/-- Tsaturian's lower bound [Ts17] (SOLVED; not proved here): no colouring works with `k ≤ 5`. -/
theorem erdos_problem_188.variants.tsaturian :
    ∀ k : ℕ, k ≤ 5 → ¬ ∃ f : EuclideanSpace ℝ (Fin 2) → Bool,
      (∀ x y : EuclideanSpace ℝ (Fin 2), f x = true → f y = true → ‖x - y‖ = 1 → False) ∧
      (∀ (p v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → ¬∀ i : Fin k, f (p + (i : ℕ) • v) = false) :=
  sorry

/-- Erdős and Graham's claim (stated without proof, per the page; OPEN): `k = 10⁷` works. It
implies the main theorem. -/
theorem erdos_problem_188.variants.erdos_graham_claim :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Bool,
      (∀ x y : EuclideanSpace ℝ (Fin 2), f x = true → f y = true → ‖x - y‖ = 1 → False) ∧
      (∀ (p v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
        ¬∀ i : Fin 10000000, f (p + (i : ℕ) • v) = false) :=
  sorry

/-- The unit vector along the first axis. -/
noncomputable def e188 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

/-- `e188` has norm `1` (PROVED in Lean). -/
theorem erdos_problem_188.norm_e188 : ‖e188‖ = 1 := by
  simp [e188]

/-- `k = 1` is impossible: with no blue point allowed, two points at distance `1` would both be
red (PROVED in Lean). -/
theorem erdos_problem_188.variants.not_one :
    ¬ ∃ f : EuclideanSpace ℝ (Fin 2) → Bool,
      (∀ x y : EuclideanSpace ℝ (Fin 2), f x = true → f y = true → ‖x - y‖ = 1 → False) ∧
      (∀ (p v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → ¬∀ i : Fin 1, f (p + (i : ℕ) • v) = false) := by
  rintro ⟨f, hred, hblue⟩
  have hall : ∀ p, f p = true := by
    intro p
    by_contra h
    apply hblue p e188 erdos_problem_188.norm_e188
    intro i
    simpa [Fin.fin_one_eq_zero i] using h
  exact hred e188 0 (hall _) (hall _) (by simpa using erdos_problem_188.norm_e188)

/-- Van der Waerden's theorem for 2-colourings of `ℤ` (PROVED in Lean, from Mathlib's Hales–Jewett
theorem): every `k`-term range has a monochromatic progression with positive common difference. -/
theorem erdos_problem_188.vdw (g : ℤ → Bool) (k : ℕ) :
    ∃ a : ℤ, ∃ d : ℕ, 0 < d ∧ ∃ c : Bool, ∀ i : ℕ, i < k → g (a + i * d) = c := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, 1, one_pos, true, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Fin k) Bool
  obtain ⟨l, c, hl⟩ := hι fun v => g ((∑ i, ((v i : Fin k) : ℕ) : ℕ) : ℤ)
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
  refine ⟨(b : ℤ), s.card, hd, c, fun i hi => ?_⟩
  have h1 := hl ⟨i, hi⟩
  simp only at h1
  rw [hsum] at h1
  rw [← h1]
  congr 1
  push_cast
  ring

/-- Alon's remark (PROVED in Lean): without the distance-`1` restriction no `k` works. In every
colouring with no two red points at distance `1`, already the integer points of one line contain
blue progressions of every length. -/
theorem erdos_problem_188.variants.alon (k : ℕ) (f : EuclideanSpace ℝ (Fin 2) → Bool)
    (hred : ∀ x y : EuclideanSpace ℝ (Fin 2), f x = true → f y = true → ‖x - y‖ = 1 → False) :
    ∃ p v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ ∀ i : Fin k, f (p + (i : ℕ) • v) = false := by
  have hpt : ∀ (a : ℤ) (d i : ℕ),
      ((a : ℝ) • e188 + (i : ℕ) • ((d : ℝ) • e188)) = (((a + i * d : ℤ)) : ℝ) • e188 := by
    intro a d i
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have hne : e188 ≠ 0 := by
    intro h
    have := erdos_problem_188.norm_e188
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hnext : ∀ n : ℤ, f ((n : ℝ) • e188) = true → f (((n + 1 : ℤ) : ℝ) • e188) = false := by
    intro n hn
    by_contra h
    rw [Bool.not_eq_false] at h
    refine hred _ _ h hn ?_
    rw [Int.cast_add, Int.cast_one, ← sub_smul, add_sub_cancel_left, one_smul]
    exact erdos_problem_188.norm_e188
  obtain ⟨a, d, hd, c, hc⟩ := erdos_problem_188.vdw (fun n : ℤ => f ((n : ℝ) • e188)) k
  have hdne : ((d : ℝ) • e188) ≠ 0 :=
    smul_ne_zero (by exact_mod_cast hd.ne') hne
  cases c with
  | false =>
    refine ⟨(a : ℝ) • e188, (d : ℝ) • e188, hdne, fun i => ?_⟩
    rw [hpt]
    exact hc i i.isLt
  | true =>
    refine ⟨((a + 1 : ℤ) : ℝ) • e188, (d : ℝ) • e188, hdne, fun i => ?_⟩
    rw [hpt]
    have := hnext _ (hc i i.isLt)
    rw [show a + 1 + (i : ℕ) * (d : ℤ) = a + (i : ℕ) * d + 1 by ring]
    exact this
