-- [AI - Claude Opus 5.5]: Erdős Problem 190 — second-pass formalization
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Real

noncomputable section

/-!
# Erdős Problem #190

*Source:* [erdosproblems.com/190](https://www.erdosproblems.com/190) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20; page
edited 27 October 2025). [ErGr79, p.333] [ErGr80, p.17]

Let $H(k)$ be the smallest $N$ such that in any finite colouring of $\{1,\ldots,N\}$ (into any
number of colours) there is always either a monochromatic $k$-term arithmetic progression or a
rainbow arithmetic progression (i.e. all elements are different colours). Estimate $H(k)$. Is it
true that $H(k)^{1/k}/k \to \infty$ as $k\to\infty$?

Remarks recorded on the page: this type of problem belongs to 'canonical' Ramsey theory. The
existence of $H(k)$ follows from Szemerédi's theorem, and it is easy to show that
$H(k)^{1/k}\to\infty$.

## The defect and its fix

$H(k)$ is the canonical van der Waerden number: every colouring of $\{1,\dots,N\}$ has a $k$-term
progression that is monochromatic or rainbow. The input's `hasRainbowAP` asks only for a rainbow
**3-term** progression, which defines a different, smaller function: for example the input's `H 2`
is `3` (`H_two`, PROVED in Lean), while the page's $H(2)$ is $2$, since any two numbers form a
$2$-term progression that is monochromatic or rainbow (`canonicalH190_two`, PROVED). The page's
remark that $H(k)^{1/k}\to\infty$ is easy also fits only the $k$-term reading: $k-1$ colours admit no
rainbow $k$-term progression. v2 defines the $k$-term version (`canonicalH190`) and states the
question for it. The input's statement is kept as `variants.three_term_rainbow`.

## Status after capture

The metadata mirror (`c443d8c`) records the problem as **solved** (2026-06-02), and "solved (Lean)"
(2026-09-15): "every canonical N exceeds (Ck)^k for all large k, hence H(k)^{1/k}/k → ∞", proved in
Lean (`jbaelaw/erdos190-lean`) following Section 4.3 of arXiv:2604.20588. Neither was read in this
review. There is no upstream `formal-conjectures` file for 190.

## References

No bibliography entries are listed on the site's `/latex/190`.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/190.lean` (Opus 5.5 review, `opus-5-5-review/190.md`).
-/

/-- A colouring χ : ℕ → ℕ has a monochromatic k-term arithmetic progression
    within {1,…,N}: there exist a ≥ 1 and d ≥ 1 such that a, a+d, …,
    a+(k-1)·d are all in {1,…,N} and all share the same colour. -/
def hasMonoAP (χ : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : ℕ, i < k → χ (a + i * d) = χ a

/-- A colouring χ : ℕ → ℕ has a rainbow 3-term arithmetic progression
    within {1,…,N}: there exist a ≥ 1 and d ≥ 1 such that a, a+d, a+2d
    are all in {1,…,N} and their colours are pairwise distinct. -/
def hasRainbowAP (χ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + 2 * d ≤ N ∧
    χ a ≠ χ (a + d) ∧ χ a ≠ χ (a + 2 * d) ∧ χ (a + d) ≠ χ (a + 2 * d)

/-- H(k) is the smallest N such that any colouring of {1,…,N} contains
    either a monochromatic k-term AP or a rainbow 3-term AP. (Not the page's $H(k)$, which asks for
    a rainbow `k`-term AP; see `canonicalH190`.) -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → ℕ, hasMonoAP χ N k ∨ hasRainbowAP χ N}

/-- A colouring χ : ℕ → ℕ has a rainbow `k`-term arithmetic progression within `{1,…,N}`: its `k`
terms get pairwise distinct colours. -/
def hasRainbowKAP190 (χ : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
    ∀ i j : ℕ, i < k → j < k → i ≠ j → χ (a + i * d) ≠ χ (a + j * d)

/-- The page's $H(k)$, the canonical van der Waerden number: the smallest `N` such that every
colouring of `{1,…,N}` has a `k`-term progression that is monochromatic or rainbow. -/
noncomputable def canonicalH190 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → ℕ, hasMonoAP χ N k ∨ hasRainbowKAP190 χ N k}

/--
Erdős Problem #190 [ErGr79, ErGr80]:

$H(k)^{1/k}/k\to\infty$ as $k\to\infty$, where $H(k)$ is the canonical van der Waerden number
(`canonicalH190`): the smallest `N` such that any finite colouring of `{1,…,N}` has a `k`-term
arithmetic progression that is monochromatic or rainbow.

(Status: OPEN at capture; recorded as solved, in this direction, by the mirror; unverified here.)
-/
theorem erdos_problem_190 :
    Tendsto (fun k : ℕ => (canonicalH190 k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k : ℝ)) atTop atTop :=
  sorry

/-- The input's statement, with rainbow **3-term** progressions (status not recorded; not the
page's question). -/
theorem erdos_problem_190.variants.three_term_rainbow :
    Tendsto (fun k : ℕ => (H k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k : ℝ)) atTop atTop :=
  sorry

/-- The page's easy fact (SOLVED; not proved here): $H(k)^{1/k}\to\infty$. -/
theorem erdos_problem_190.variants.easy :
    Tendsto (fun k : ℕ => (canonicalH190 k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop :=
  sorry

/-- The input's function at `k = 2` is `3` (PROVED in Lean): `{1, 2}` coloured with two colours has
neither a monochromatic `2`-term progression nor a rainbow `3`-term one. -/
theorem erdos_problem_190.H_two : H 2 = 3 := by
  unfold H
  have h3 : (3 : ℕ) ∈ {N : ℕ | ∀ χ : ℕ → ℕ, hasMonoAP χ N 2 ∨ hasRainbowAP χ N} := by
    intro χ
    by_cases h12 : χ 2 = χ 1
    · exact Or.inl ⟨1, 1, one_pos, le_rfl, by norm_num, fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [h12]⟩
    by_cases h13 : χ 3 = χ 1
    · exact Or.inl ⟨1, 2, two_pos, le_rfl, by norm_num, fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [h13]⟩
    by_cases h23 : χ 3 = χ 2
    · exact Or.inl ⟨2, 1, one_pos, by norm_num, by norm_num, fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [h23]⟩
    exact Or.inr ⟨1, 1, one_pos, le_rfl, by norm_num, fun h => h12 h.symm, fun h => h13 h.symm,
      fun h => h23 h.symm⟩
  refine le_antisymm (Nat.sInf_le h3) (le_csInf ⟨3, h3⟩ fun n hn => ?_)
  by_contra hlt
  push_neg at hlt
  rcases hn id with ⟨a, d, hd, ha, hle, hall⟩ | ⟨a, d, hd, ha, hle, -⟩
  · have h1 := hall 1 one_lt_two
    simp only [id, one_mul] at h1
    omega
  · omega

/-- The page's $H(2)$ is `2` (PROVED in Lean): two numbers form a `2`-term progression that is
monochromatic or rainbow. -/
theorem erdos_problem_190.canonicalH190_two : canonicalH190 2 = 2 := by
  unfold canonicalH190
  have h2 : (2 : ℕ) ∈ {N : ℕ | ∀ χ : ℕ → ℕ, hasMonoAP χ N 2 ∨ hasRainbowKAP190 χ N 2} := by
    intro χ
    by_cases h12 : χ 2 = χ 1
    · exact Or.inl ⟨1, 1, one_pos, le_rfl, by norm_num, fun i hi => by
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp [h12]⟩
    · refine Or.inr ⟨1, 1, one_pos, le_rfl, by norm_num, fun i j hi hj hij => ?_⟩
      rcases (show (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) by omega) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using Ne.symm h12
      · simpa using h12
  refine le_antisymm (Nat.sInf_le h2) (le_csInf ⟨2, h2⟩ fun n hn => ?_)
  by_contra hlt
  push_neg at hlt
  rcases hn id with ⟨a, d, hd, ha, hle, -⟩ | ⟨a, d, hd, ha, hle, -⟩ <;> omega

end
