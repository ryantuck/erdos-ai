-- [AI - Claude Opus 5.5]: Erdős Problem 185 — second-pass formalization
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

/-!
# Erdős Problem #185

*Source:* [erdosproblems.com/185](https://www.erdosproblems.com/185) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20). [Er73]

Let $f_3(n)$ be the maximal size of a subset of $\{0,1,2\}^n$ which contains no three points on a
line. Is it true that $f_3(n)=o(3^n)$?

Remarks recorded on the page (abridged): originally considered by Moser. It is trivial that
$f_3(n)\geq R_3(3^n)$, the maximal size of a subset of $\{1,\ldots,3^n\}$ without a three-term
arithmetic progression. Moser showed that $f_3(n)\gg 3^n/\sqrt{n}$. The answer is yes, which is a
corollary of the density Hales–Jewett theorem, proved by Furstenberg and Katznelson [FuKa91].
OEIS A003142.

## Encoding notes

* The page's "three points on a line" are three collinear points of $\{0,1,2\}^n\subset\mathbb R^n$
  (Moser's cube problem; OEIS A003142 is $1,2,6,16,43,\dots$). These are more general than the
  *combinatorial lines* of the input: in a geometric line the active coordinates may run
  $0,1,2$ or $2,1,0$, so for example $(0,2),(1,1),(2,0)$ is collinear but not a combinatorial line.
  For $n=3$ the largest set with no combinatorial line has 18 points, while the largest with no
  three collinear points has 16 (exhaustive search in the review).
* The input's theorem is the density Hales–Jewett theorem for $k=3$ (combinatorial lines), which
  is the result the page cites. It is strictly stronger in form than the page's question, and
  implies it: `variants.page_statement_of_main` (PROVED in Lean) derives $f_3(n)=o(3^n)$, with
  $f_3$ defined by geometric collinearity (`f3_185`), from the input's statement. The input's
  docstring calls the two "equivalent"; only the implication holds in general.

## References

From the site's `/latex/185` bibliography:
* [FuKa91] Furstenberg, H. and Katznelson, Y., _A density version of the Hales–Jewett Theorem_.
  J. Analyse Math. (1991), 64–119.

Other sources:
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138. (Site `/latex/783` and others.)

*Provenance:* second pass of `conjectures/185.lean` (Opus 5.5 review, `opus-5-5-review/185.md`).
-/

/-- A combinatorial line in {0,1,2}^n consists of three points parameterized by
j ∈ {0,1,2}, such that there exists a nonempty set S of "active" coordinates
where the j-th point has value j at each active coordinate, and all three points
agree at non-active coordinates. -/
def IsCombinatorialLine (n : ℕ) (p : Fin 3 → (Fin n → Fin 3)) : Prop :=
  ∃ (S : Finset (Fin n)), S.Nonempty ∧
    ∃ (c : Fin n → Fin 3),
      ∀ (j : Fin 3) (i : Fin n),
        p j i = if i ∈ S then j else c i

/--
Erdős Problem #185 (Density Hales-Jewett for k=3) [Er73]:

For every ε > 0, there exists N such that for all n ≥ N, every subset A ⊆ {0,1,2}^n
of size |A| > ε · 3^n contains a combinatorial line.

This implies (it is not equivalent to) the page's statement $f_3(n)=o(3^n)$, where $f_3$ counts
points with no three on a geometric line (`variants.page_statement_of_main`). Proved by
Furstenberg and Katznelson [FuKa91]. (Status: PROVED; the true direction.)
-/
theorem erdos_problem_185 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ A : Finset (Fin n → Fin 3),
          (A.card : ℝ) > ε * (3 : ℝ) ^ n →
          ∃ p : Fin 3 → (Fin n → Fin 3),
            IsCombinatorialLine n p ∧ ∀ j : Fin 3, p j ∈ A :=
  sorry

/-- The point of $\mathbb R^n$ with the same coordinates as `x ∈ {0,1,2}ⁿ`. -/
def toReal185 {n : ℕ} (x : Fin n → Fin 3) : Fin n → ℝ := fun i => ((x i : ℕ) : ℝ)

/-- The page's $f_3(n)$ (Moser's cube problem): the maximal size of a subset of $\{0,1,2\}^n$ with
no three distinct points on a line of $\mathbb R^n$. -/
noncomputable def f3_185 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset (Fin n → Fin 3),
    (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ ({toReal185 x, toReal185 y, toReal185 z} : Set (Fin n → ℝ))) ∧ A.card = m}

/-- The three points of a combinatorial line are distinct and collinear in $\mathbb R^n$ (PROVED in
Lean). -/
theorem erdos_problem_185.collinear_of_isCombinatorialLine {n : ℕ}
    {p : Fin 3 → (Fin n → Fin 3)} (hp : IsCombinatorialLine n p) :
    p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 1 ≠ p 2 ∧
      Collinear ℝ ({toReal185 (p 0), toReal185 (p 1), toReal185 (p 2)} : Set (Fin n → ℝ)) := by
  obtain ⟨S, ⟨i₀, hi₀⟩, c, hc⟩ := hp
  have hval : ∀ j : Fin 3, p j i₀ = j := fun j => by rw [hc j i₀, if_pos hi₀]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, ?_⟩
  · have h' := congrFun h i₀
    rw [hval, hval] at h'
    exact absurd h' (by decide)
  · have h' := congrFun h i₀
    rw [hval, hval] at h'
    exact absurd h' (by decide)
  · have h' := congrFun h i₀
    rw [hval, hval] at h'
    exact absurd h' (by decide)
  · rw [collinear_iff_of_mem (Set.mem_insert _ _)]
    refine ⟨fun i => if i ∈ S then (1 : ℝ) else 0, ?_⟩
    have key : ∀ j : Fin 3, toReal185 (p j) =
        (((j : ℕ) : ℝ) • (fun i => if i ∈ S then (1 : ℝ) else 0)) +ᵥ toReal185 (p 0) := by
      intro j
      funext i
      simp only [toReal185, vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc]
      split_ifs <;> simp
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨((0 : Fin 3) : ℕ), key 0⟩
    · exact ⟨((1 : Fin 3) : ℕ), key 1⟩
    · exact ⟨((2 : Fin 3) : ℕ), key 2⟩

/-- `f3_185 n` is attained: some set with no three collinear points has exactly `f3_185 n` points
(PROVED in Lean). -/
theorem erdos_problem_185.f3_185_mem (n : ℕ) :
    f3_185 n ∈ {m : ℕ | ∃ A : Finset (Fin n → Fin 3),
      (∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → x ≠ z → y ≠ z →
        ¬ Collinear ℝ ({toReal185 x, toReal185 y, toReal185 z} : Set (Fin n → ℝ))) ∧
      A.card = m} := by
  unfold f3_185
  refine Nat.sSup_mem ⟨0, ∅, by simp, rfl⟩ ⟨3 ^ n, ?_⟩
  rintro m ⟨A, -, rfl⟩
  simpa using A.card_le_univ

/-- The input's theorem implies the page's statement $f_3(n)=o(3^n)$ for geometric lines (PROVED in
Lean): a set with no three collinear points has no combinatorial line. -/
theorem erdos_problem_185.variants.page_statement_of_main
    (h : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ A : Finset (Fin n → Fin 3),
      (A.card : ℝ) > ε * (3 : ℝ) ^ n →
      ∃ p : Fin 3 → (Fin n → Fin 3), IsCombinatorialLine n p ∧ ∀ j : Fin 3, p j ∈ A) :
    (fun n : ℕ => (f3_185 n : ℝ)) =o[Filter.atTop] fun n : ℕ => (3 : ℝ) ^ n := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (by positivity)]
  obtain ⟨A, hA, hcard⟩ := erdos_problem_185.f3_185_mem n
  rw [← hcard]
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hp, hpA⟩ := hN n hn A hlt
  obtain ⟨h01, h02, h12, hcol⟩ := erdos_problem_185.collinear_of_isCombinatorialLine hp
  exact hA _ (hpA 0) _ (hpA 1) _ (hpA 2) h01 h02 h12 hcol

/-- Moser's lower bound $f_3(n)\gg3^n/\sqrt n$ (SOLVED; not proved here). -/
theorem erdos_problem_185.variants.moser :
    (fun n : ℕ => (3 : ℝ) ^ n / Real.sqrt n) =O[Filter.atTop] fun n : ℕ => (f3_185 n : ℝ) :=
  sorry

end
