-- [AI - Claude Sonnet 5.5]: Erdős Problem 158 — second-pass formalization
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.LiminfLimsup
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card

open Filter

noncomputable section

/-!
# Erdős Problem #158: Must an infinite $B_2[2]$ set have $\liminf\lvert A\cap[1,N]\rvert/\sqrt N=0$?

*Source:* [erdosproblems.com/158](https://www.erdosproblems.com/158) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; captured 2026-03-05 as the page and as the tidied problem box, with identical
content; the page shows no edit date, "Formalised statement? Yes" and 1 comment, not captured). [ESS94]

Let $A\subset\mathbb{N}$ be an infinite set such that, for any $n$, there are most $2$ solutions to $a+b=n$ with
$a\leq b$. Must
$$\liminf_{N\to\infty}\frac{\lvert A\cap \{1,\ldots,N\}\rvert}{N^{1/2}}=0?$$
(The page's text reads "most" where "at most" is meant.)

Remark recorded on the page (first-person plural reworded): replacing $2$ by $1$ makes $A$ a Sidon set, for which Erdős
proved this is true.

Tags: sidon sets.

**Status.** OPEN. The mirror (`teorth/erdosproblems`, `b916d95`) has `open` since 2025-08-31, no prize, formalised `yes`
(2026-01-04); upstream's `158.lean` (`df3f12d`) has `erdos_158` as `research open`, in the form
`answer(sorry) ↔ ∀ A, A.Infinite → B2 2 A → liminf (fun N ↦ (A ∩ .Iio N).ncard * N ^ (-1 / 2)) atTop = 0`, with the Sidon case
as sorry'd solved variants.

**Encoding.**
* `repCount A n` is the number of pairs `(a, b)` with `a, b ∈ A`, `a ≤ b` and `a + b = n`; the hypothesis says it is at most
  `2` for every `n`, which is the page's "at most 2 solutions with $a\le b$". The set of pairs is finite (both entries are at
  most `n`), so `Set.ncard` is the true count. `variants.repCount_le_one_iff` proves in Lean that the bound `1` is exactly the
  Sidon property in the form used for Problems 152–157, which is the page's remark about replacing `2` by `1`.
* `countBelow A N` is `|A ∩ {1, …, N}|`, the cardinality of a finite set.
* The statement says: every infinite set `A ⊆ ℕ` with `repCount A n ≤ 2` for all `n` has `liminf |A ∩ {1, …, N}| / √N = 0`.
  The page asks "Must …?", so the asked direction ("yes") is asserted, since the problem is open.
* `Filter.liminf` of a real sequence is meaningful only for a bounded sequence. `variants.count_sq_le` proves that a set
  with `repCount A n ≤ 2` has `|A ∩ {1, …, N}|² ≤ 8N + 4`, so the quotient is at most `4` (`variants.bounded`) and the
  `liminf` is the genuine one. `variants.main_iff_frequently` proves that it is `0` iff for every `ε > 0` there are
  infinitely many `N` with `|A ∩ {1, …, N}| < ε √N`.
* `A : Set ℕ` may contain `0`, which `countBelow` ignores. `variants.positive_version` proves that the statement is
  equivalent to the one for sets of positive integers.
* The hypotheses are satisfiable, so the statement is not vacuous: `variants.hypotheses_satisfiable` proves that the set
  `{2^n - 1}` is infinite with `repCount ≤ 1`, hence `≤ 2`.
* `variants.sidon_case` is the page's remark, Erdős's result for `repCount ≤ 1`, as a variant with `sorry`. It is SOLVED in
  the literature and is not proved here. **DEFERRED:** the page gives no reference for it, and the proof was not seen.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From the
  `/latex/156` fetch in the session logs, the site's bibliography for another problem; upstream's docstring agrees.
  **DEFERRED:** there is no `/latex/158` fetch, so this problem's own bibliography was not seen.)
-/

/--
The number of representations of n as a + b with a ≤ b and a, b ∈ A.
-/
def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/--
The counting function |A ∩ {1, …, N}|.
-/
noncomputable def countBelow (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/--
Erdős Problem #158 [ESS94] (OPEN):

Let A ⊆ ℕ be an infinite set such that, for any n, there are at most 2
solutions to a + b = n with a ≤ b and a, b ∈ A (i.e., A is a B₂[2] set).
Must
  lim inf_{N → ∞} |A ∩ {1, …, N}| / N^{1/2} = 0?

Replacing 2 by 1 makes A a Sidon set, for which Erdős proved this is true.
-/
theorem erdos_problem_158
    (A : Set ℕ)
    (hA_inf : A.Infinite)
    (hA_rep : ∀ n : ℕ, repCount A n ≤ 2) :
    Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 :=
  sorry

/-- The set of representations of `n` is finite, so `repCount` is the true number of representations (PROVED in Lean). -/
theorem erdos_problem_158.repSet_finite (A : Set ℕ) (n : ℕ) :
    {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}.Finite := by
  refine Set.Finite.subset (Finset.finite_toSet (Finset.range (n + 1) ×ˢ Finset.range (n + 1))) ?_
  intro p hp
  obtain ⟨-, -, h1, h2⟩ := hp
  simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
  omega

/-- A set with at most two representations of every `n` has `|A ∩ {1, …, N}|² ≤ 8N + 4` (PROVED in Lean): the ordered
pairs of elements of `A ∩ {1, …, N}` have sums in `{0, …, 2N}`, and each sum has at most `4` ordered representations. -/
theorem erdos_problem_158.variants.count_sq_le (A : Set ℕ) (hA : ∀ n, repCount A n ≤ 2) (N : ℕ) :
    (countBelow A N) ^ 2 ≤ 8 * N + 4 := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ A) with hS
  have hcount : countBelow A N = S.card := by
    unfold countBelow
    have : A ∩ Set.Icc 1 N = (S : Set ℕ) := by
      ext x
      simp only [hS, Set.mem_inter_iff, Set.mem_Icc, Finset.coe_filter, Finset.mem_Icc,
        Set.mem_setOf_eq]
      tauto
    rw [this, Set.ncard_coe_finset]
  rw [hcount]
  have hfiber : ∀ n, ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card ≤ 4 := by
    intro n
    set U : Finset (ℕ × ℕ) := (S ×ˢ S).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) with hU
    have hUcard : U.card ≤ 2 := by
      have hsub : (U : Set (ℕ × ℕ)) ⊆
          {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n} := by
        intro p hp
        simp only [hU, Finset.coe_filter, Finset.mem_product, hS, Finset.mem_filter,
          Set.mem_setOf_eq] at hp
        exact ⟨hp.1.1.2, hp.1.2.2, hp.2.1, hp.2.2⟩
      calc U.card = (U : Set (ℕ × ℕ)).ncard := (Set.ncard_coe_finset U).symm
        _ ≤ repCount A n := Set.ncard_le_ncard hsub (erdos_problem_158.repSet_finite A n)
        _ ≤ 2 := hA n
    have hcov : (S ×ˢ S).filter (fun p => p.1 + p.2 = n) ⊆ U ∪ U.image Prod.swap := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_product] at hp
      rcases le_total p.1 p.2 with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr hp.1, h, hp.2⟩)
      · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p.swap, ?_, by simp⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1.2, hp.1.1⟩, h,
          by simpa [add_comm] using hp.2⟩
    calc ((S ×ˢ S).filter (fun p => p.1 + p.2 = n)).card
        ≤ (U ∪ U.image Prod.swap).card := Finset.card_le_card hcov
      _ ≤ U.card + (U.image Prod.swap).card := Finset.card_union_le _ _
      _ ≤ U.card + U.card := by
          have := Finset.card_image_le (s := U) (f := Prod.swap)
          omega
      _ ≤ 4 := by omega
  have hmain : (S ×ˢ S).card ≤ 4 * ((S ×ˢ S).image (fun p => p.1 + p.2)).card :=
    Finset.card_le_mul_card_image (S ×ˢ S) 4 (fun b _ => hfiber b)
  have himage : ((S ×ˢ S).image (fun p => p.1 + p.2)) ⊆ Finset.range (2 * N + 1) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simp only [hS, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_range]
    omega
  have h2 := Finset.card_le_card himage
  rw [Finset.card_product] at hmain
  simp only [Finset.card_range] at h2
  nlinarith

/-- For a set with at most two representations of every `n`, the quotient is at most `4` (PROVED in Lean), so the
`liminf` in the main theorem is the genuine one and not a junk value of `ℝ`. -/
theorem erdos_problem_158.variants.bounded (A : Set ℕ) (hA : ∀ n, repCount A n ≤ 2) (N : ℕ) :
    (countBelow A N : ℝ) / Real.sqrt (N : ℝ) ≤ 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hsq := erdos_problem_158.variants.count_sq_le A hA N
    have hNpos : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
    rw [div_le_iff₀ hNpos]
    have h1 : ((countBelow A N : ℝ)) ^ 2 ≤ 8 * N + 4 := by exact_mod_cast hsq
    have h2 : (4 * Real.sqrt (N : ℝ)) ^ 2 = 16 * N := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]; norm_num
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    by_contra hcon
    push_neg at hcon
    have := pow_lt_pow_left₀ hcon (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
    linarith

/-- The conclusion of the main theorem is "for every `ε > 0`, `|A ∩ {1, …, N}| < ε √N` for infinitely many `N`"
(PROVED in Lean), for a set with at most two representations of every `n`. -/
theorem erdos_problem_158.variants.main_iff_frequently (A : Set ℕ) (hA : ∀ n, repCount A n ≤ 2) :
    Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 ↔
    ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (countBelow A N : ℝ) / Real.sqrt (N : ℝ) < ε := by
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) :=
    ⟨4, Filter.eventually_map.mpr
      (Filter.Eventually.of_forall fun N => erdos_problem_158.variants.bounded A hA N)⟩
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) := hbdd.isCoboundedUnder_flip
  have hlow : IsBoundedUnder (· ≥ ·) atTop
      (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) :=
    ⟨0, Filter.eventually_map.mpr (Filter.Eventually.of_forall fun N => by positivity)⟩
  have hnonneg : 0 ≤ Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop :=
    Filter.le_liminf_of_le hcob (Filter.Eventually.of_forall fun N => by positivity)
  constructor
  · intro h ε hε
    exact Filter.frequently_lt_of_liminf_lt hcob (by rw [h]; exact hε)
  · intro h
    refine le_antisymm ?_ hnonneg
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := Filter.liminf_le_of_frequently_le ((h ε hε).mono fun N hN => hN.le) hlow
    linarith

/-- At most one representation of every `n` is exactly the Sidon property in the four-variable form used for
Problems 152–157 (PROVED in Lean): the page's remark that replacing `2` by `1` gives a Sidon set. -/
theorem erdos_problem_158.variants.repCount_le_one_iff (A : Set ℕ) :
    (∀ n, repCount A n ≤ 1) ↔
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h a ha b hb c hc d hd hab
    have key := (Set.ncard_le_one (erdos_problem_158.repSet_finite A (a + b))).mp (h (a + b))
    have hp : (min a b, max a b) ∈
        {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = a + b} := by
      refine ⟨?_, ?_, min_le_max, min_add_max a b⟩
      · rcases le_total a b with h' | h' <;> simp [h', ha, hb]
      · rcases le_total a b with h' | h' <;> simp [h', ha, hb]
    have hq : (min c d, max c d) ∈
        {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = a + b} := by
      refine ⟨?_, ?_, min_le_max, by rw [min_add_max c d]; omega⟩
      · rcases le_total c d with h' | h' <;> simp [h', hc, hd]
      · rcases le_total c d with h' | h' <;> simp [h', hc, hd]
    have := key _ hp _ hq
    simp only [Prod.mk.injEq] at this
    omega
  · intro h n
    rw [repCount, Set.ncard_le_one_iff (erdos_problem_158.repSet_finite A n)]
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hb, hab, hsum⟩ ⟨hc, hd, hcd, hsum'⟩
    simp only at ha hb hab hsum hc hd hcd hsum'
    rcases h a ha b hb c hc d hd (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · exact Prod.ext (by simp only; omega) (by simp only; omega)

/-- Allowing `0 ∈ A` changes nothing: `countBelow` ignores `0`, so the main statement is equivalent to the one for sets
of positive integers (PROVED in Lean). -/
theorem erdos_problem_158.variants.positive_version :
    (∀ A : Set ℕ, A.Infinite → (∀ n, repCount A n ≤ 2) →
      Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0) ↔
    ∀ A : Set ℕ, (∀ a ∈ A, 1 ≤ a) → A.Infinite → (∀ n, repCount A n ≤ 2) →
      Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 := by
  constructor
  · intro h A _ hinf hrep
    exact h A hinf hrep
  · intro h A hinf hrep
    have hcount : ∀ N, countBelow (A \ {0}) N = countBelow A N := by
      intro N
      unfold countBelow
      congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff, Set.mem_Icc]
      constructor
      · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
    have hrep' : ∀ n, repCount (A \ {0}) n ≤ 2 := by
      intro n
      refine le_trans ?_ (hrep n)
      apply Set.ncard_le_ncard _ (erdos_problem_158.repSet_finite A n)
      rintro ⟨a, b⟩ ⟨ha, hb, hab, hsum⟩
      exact ⟨ha.1, hb.1, hab, hsum⟩
    have := h (A \ {0}) (fun a ha => by
        have := ha.2
        simp only [Set.mem_singleton_iff] at this
        omega)
      (hinf.diff (Set.finite_singleton 0)) hrep'
    simpa only [hcount] using this

/-- A set `A ⊆ ℕ` is a Sidon set if all pairwise sums are distinct (the four-variable form used for Problems 152–157,
here for sets that may be infinite). -/
def erdos_problem_158.IsSidon (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Adding an element larger than twice the maximum to a Sidon set keeps it Sidon (PROVED in Lean). -/
theorem erdos_problem_158.sidon_insert_large {A : Set ℕ} {M : ℕ}
    (hA : erdos_problem_158.IsSidon A) (hM : ∀ y ∈ A, y ≤ M) :
    erdos_problem_158.IsSidon (insert (2 * M + 1) A) := by
  intro a ha b hb c hc d hd h
  have key : ∀ y, y ∈ insert (2 * M + 1) A → y = 2 * M + 1 ∨ (y ∈ A ∧ y ≤ M) := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hM y h⟩
  rcases key a ha with rfl | ⟨ha1, ha2⟩ <;> rcases key b hb with rfl | ⟨hb1, hb2⟩ <;>
    rcases key c hc with rfl | ⟨hc1, hc2⟩ <;> rcases key d hd with rfl | ⟨hd1, hd2⟩ <;>
    first
    | omega
    | exact hA _ ha1 _ hb1 _ hc1 _ hd1 h

/-- The sequence `0, 1, 3, 7, 15, …` (`2^n - 1`), each term twice the previous one plus one. -/
def erdos_problem_158.doubling : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * erdos_problem_158.doubling n + 1

/-- The doubling sequence is strictly increasing (PROVED in Lean). -/
theorem erdos_problem_158.doubling_strictMono : StrictMono erdos_problem_158.doubling :=
  strictMono_nat_of_lt_succ fun n => by
    simp only [erdos_problem_158.doubling]
    omega

/-- The first terms of the doubling sequence form a Sidon set (PROVED in Lean). -/
theorem erdos_problem_158.sidon_doubling_le (m : ℕ) :
    erdos_problem_158.IsSidon (erdos_problem_158.doubling '' Set.Iic m) := by
  induction m with
  | zero =>
    have : erdos_problem_158.doubling '' Set.Iic 0 = {0} := by
      ext x; simp [erdos_problem_158.doubling, eq_comm]
    rw [this]
    intro a ha b hb c hc d hd h
    simp only [Set.mem_singleton_iff] at ha hb hc hd
    subst ha; subst hb; subst hc; subst hd
    exact Or.inl ⟨rfl, rfl⟩
  | succ m ih =>
    have : erdos_problem_158.doubling '' Set.Iic (m + 1) =
        insert (2 * erdos_problem_158.doubling m + 1)
          (erdos_problem_158.doubling '' Set.Iic m) := by
      ext x
      simp only [Set.mem_image, Set.mem_Iic, Set.mem_insert_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        rcases Nat.lt_or_ge i (m + 1) with h | h
        · exact Or.inr ⟨i, by omega, rfl⟩
        · have : i = m + 1 := by omega
          subst this
          exact Or.inl rfl
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨m + 1, le_refl _, rfl⟩
        · exact ⟨i, by omega, rfl⟩
    rw [this]
    refine erdos_problem_158.sidon_insert_large ih ?_
    rintro _ ⟨i, hi, rfl⟩
    exact erdos_problem_158.doubling_strictMono.monotone hi

/-- The set `{2^n - 1}` is an infinite-type Sidon set: any four of its elements lie among its first terms (PROVED in
Lean). -/
theorem erdos_problem_158.sidon_doubling :
    erdos_problem_158.IsSidon (Set.range erdos_problem_158.doubling) := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ h
  have hmem : ∀ x, x ≤ max (max i j) (max k l) →
      erdos_problem_158.doubling x ∈
        erdos_problem_158.doubling '' Set.Iic (max (max i j) (max k l)) :=
    fun x hx => ⟨x, hx, rfl⟩
  exact erdos_problem_158.sidon_doubling_le (max (max i j) (max k l))
    _ (hmem i (by omega)) _ (hmem j (by omega)) _ (hmem k (by omega)) _ (hmem l (by omega)) h

/-- The hypotheses of the main theorem are satisfiable (PROVED in Lean): `{2^n - 1}` is infinite with at most one
representation of every `n`, hence at most two. So the statement is not vacuous. -/
theorem erdos_problem_158.variants.hypotheses_satisfiable :
    ∃ A : Set ℕ, A.Infinite ∧ ∀ n, repCount A n ≤ 2 := by
  refine ⟨Set.range erdos_problem_158.doubling,
    Set.infinite_range_of_injective erdos_problem_158.doubling_strictMono.injective, fun n => ?_⟩
  have := (erdos_problem_158.variants.repCount_le_one_iff _).mpr
    erdos_problem_158.sidon_doubling n
  omega

/-- Erdős's theorem for Sidon sets, the page's remark (SOLVED in the literature, not proved here): an infinite set with at
most one representation of every `n` has `liminf |A ∩ {1, …, N}| / √N = 0`. -/
theorem erdos_problem_158.variants.sidon_case (A : Set ℕ) (hA_inf : A.Infinite)
    (hA_rep : ∀ n : ℕ, repCount A n ≤ 1) :
    Filter.liminf (fun N : ℕ => (countBelow A N : ℝ) / Real.sqrt (N : ℝ)) atTop = 0 :=
  sorry

end
