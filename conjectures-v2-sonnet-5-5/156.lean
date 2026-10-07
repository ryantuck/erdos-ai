-- [AI - Claude Sonnet 5.5]: Erdős Problem 156 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Real Finset Topology

noncomputable section

/-!
# Erdős Problem #156: Is there a maximal Sidon set of size $O(N^{1/3})$?

*Source:* [erdosproblems.com/156](https://www.erdosproblems.com/156) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; captured 2026-02-20 as the page and as the tidied problem box, with identical
content; the page shows no edit date, "Formalised statement? No" at that time, 0 comments, and lists the OEIS sequence
A382397, not fetched). [ESS94]

Does there exist a maximal Sidon set $A\subset \{1,\ldots,N\}$ of size $O(N^{1/3})$?

Remarks recorded on the page: A question of Erdős, Sárközy, and Sós [ESS94]. It is easy to prove that the greedy
construction of a maximal Sidon set in $\{1,\ldots,N\}$ has size $\gg N^{1/3}$. Ruzsa [Ru98b] constructed a maximal Sidon
set of size $\ll (N\log N)^{1/3}$. See also [340].

Tags: sidon sets.

**Status.** OPEN. The mirror (`teorth/erdosproblems`, `b916d95`) has `open` since 2025-08-31, no prize, formalised `yes`
(2026-06-21, after the capture); upstream's `156.lean` (`df3f12d`) has `erdos_156` as `research open`, in the form
`answer(sorry) ↔ (fun N ↦ (minMaximalSidonSet N : ℝ)) =O[atTop] (fun N ↦ (N : ℝ) ^ (1 / 3 : ℝ))`, with the two bounds of the
remarks as sorry'd solved variants.

**Encoding.**
* `IsSidonSet A` says that every sum `a + b` with `a, b ∈ A` determines the pair `{a, b}`, as in Problems 152–155.
* `IsMaximalSidonSet N A` says that `A ⊆ {0, …, N - 1}` is Sidon and no `n ∈ {0, …, N - 1} \ A` can be added to `A` while
  keeping it Sidon. The Sidon property and maximality in the interval are invariant under translation, so this is the page's
  notion for `{1, …, N}`.
* The statement says: there is `C > 0` such that for all large `N` some maximal Sidon set in `{0, …, N - 1}` has at most
  `C * N^(1/3)` elements. `variants.main_iff_min` proves that this is `minMaximalSidon N = O(N^(1/3))`, upstream's form, for
  `minMaximalSidon N` the least size of a maximal Sidon subset of `{0, …, N - 1}`, and `exists_maximal` proves that a maximal
  Sidon set exists for every `N`, so that minimum is over a nonempty family.
* The asked direction ("yes") is asserted, since the problem is open and the page asks a yes/no question. The page calls it
  a question of Erdős, Sárközy and Sós, not a conjecture, so the statement records the corpus convention for open questions
  and makes no claim about what the authors expected.
* `variants.card_bound` proves in Lean that every maximal Sidon set `A` in `{0, …, N - 1}` satisfies
  `N ≤ |A| + |A|² + |A|³`, since every `x ∉ A` in the interval is `c + d - a` or `(c + d) / 2` for some `a, c, d ∈ A`, and
  `variants.lower_bound` deduces `|A| ≥ N^(1/3) / 2`. This is the page's "easy" lower bound, for every maximal Sidon set and
  not only for the greedy one. So the question is whether the lower bound is attained up to a constant.
* `variants.ruzsa_upper` is Ruzsa's bound [Ru98b] as a variant with `sorry`. It is SOLVED in the literature and is not
  proved here. **DEFERRED:** the paper was not seen.
* `variants.maximal_not_maximum` shows that maximal is weaker than maximum: `{1, 2, 5}` and `{0, 1, 4, 6}` are both maximal in
  `{0, …, 6}`. `variants.minMaximalSidon_five` and `minMaximalSidon_seven` evaluate the minimum for `N = 5, 7`. An exhaustive
  search outside Lean gives it for larger `N` and is in the review.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From the
  `/latex/156` fetch in the session logs, the site's bibliography for this problem.)
* [Ru98b] Ruzsa, I. Z., _A small maximal Sidon set_. Ramanujan J. (1998), 55–58. (From the same fetch.)
* [340] Problem 340 of the site, on the greedy Sidon sequence (cross-reference only).
* **DEFERRED:** the two papers and the page of Problem 340 were not seen, and neither was OEIS A382397.
-/

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, then {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon set A ⊆ {0, ..., N-1} is maximal (in {0, ..., N-1}) if no element of
    {0, ..., N-1} \ A can be added to A while preserving the Sidon property. -/
def IsMaximalSidonSet (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range N ∧
  IsSidonSet A ∧
  ∀ n ∈ Finset.range N, n ∉ A → ¬IsSidonSet (insert n A)

/--
Erdős Problem #156 [ESS94] (OPEN):

Does there exist a maximal Sidon set $A \subset \{1, \ldots, N\}$ of size $O(N^{1/3})$?

The formal statement asserts the asked direction (YES), as the corpus does for open questions; the page calls this a
question and not a conjecture.

The greedy algorithm produces a maximal Sidon set of size $\gg N^{1/3}$ (this is known).
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$, which is
close but does not reach $O(N^{1/3})$.

Formalized as: there exists a constant $C > 0$ such that for all sufficiently large $N$,
there exists a maximal Sidon set $A \subseteq \{0, \ldots, N-1\}$ with
$|A| \leq C \cdot N^{1/3}$.
-/
theorem erdos_problem_156 :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧
          (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  sorry

/-- Being a Sidon set is decidable (used to evaluate the examples below by `decide`). -/
instance (A : Finset ℕ) : Decidable (IsSidonSet A) := by
  unfold IsSidonSet; infer_instance

/-- Being a maximal Sidon set in `{0, …, N - 1}` is decidable (used to evaluate the examples below by `decide`). -/
instance (N : ℕ) (A : Finset ℕ) : Decidable (IsMaximalSidonSet N A) := by
  unfold IsMaximalSidonSet; infer_instance

/-- `minMaximalSidon N` is the least size of a maximal Sidon subset of `{0, …, N - 1}`. By `exists_maximal` the family is
nonempty, so this is a true minimum (`exists_min`). -/
def minMaximalSidon (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧ A.card = k}

/-- A subset of a Sidon set is a Sidon set (PROVED in Lean). -/
theorem erdos_problem_156.sidon_mono {A B : Finset ℕ} (hB : IsSidonSet B) (h : A ⊆ B) :
    IsSidonSet A :=
  fun a ha b hb c hc d hd => hB a (h ha) b (h hb) c (h hc) d (h hd)

/-- For every `N` there is a maximal Sidon set in `{0, …, N - 1}` (PROVED in Lean): a Sidon subset of largest size is
maximal. -/
theorem erdos_problem_156.exists_maximal (N : ℕ) : ∃ A : Finset ℕ, IsMaximalSidonSet N A := by
  have hne : (((Finset.range N).powerset).filter (fun A => IsSidonSet A)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, fun a ha => absurd ha (by simp)⟩⟩
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image _ Finset.card hne
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, fun n hn hnA hS => ?_⟩
  have := hmax (insert n A) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
    (Finset.insert_subset hn hA.1), hS⟩)
  rw [Finset.card_insert_of_notMem hnA] at this
  omega

/-- An element `x ∉ A` can be added to a Sidon set `A` unless `x + x = c + d` or `x + a = c + d` for some `a, c, d ∈ A`
(PROVED in Lean). -/
theorem erdos_problem_156.sidon_insert {A : Finset ℕ} {x : ℕ} (hA : IsSidonSet A) (hx : x ∉ A)
    (h1 : ∀ c ∈ A, ∀ d ∈ A, x + x ≠ c + d)
    (h2 : ∀ a ∈ A, ∀ c ∈ A, ∀ d ∈ A, x + a ≠ c + d) : IsSidonSet (insert x A) := by
  intro a ha b hb c hc d hd h
  have key : ∀ y, y ∈ insert x A → y = x ∨ (y ∈ A ∧ y ≠ x) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, fun e => hx (e ▸ h)⟩
  rcases key a ha with rfl | ⟨ha1, ha2⟩ <;> rcases key b hb with rfl | ⟨hb1, hb2⟩ <;>
    rcases key c hc with rfl | ⟨hc1, hc2⟩ <;> rcases key d hd with rfl | ⟨hd1, hd2⟩ <;>
    first
    | omega
    | exact hA _ ha1 _ hb1 _ hc1 _ hd1 h
    | exact (h1 _ hc1 _ hd1 h).elim
    | exact (h1 _ ha1 _ hb1 h.symm).elim
    | exact (h2 _ hb1 _ hc1 _ hd1 h).elim
    | exact (h2 _ ha1 _ hc1 _ hd1 (by omega)).elim
    | exact (h2 _ hd1 _ ha1 _ hb1 h.symm).elim
    | exact (h2 _ hc1 _ ha1 _ hb1 (by omega)).elim

/-- The minimum is at most the size of any maximal Sidon set (PROVED in Lean). -/
theorem erdos_problem_156.minMaximalSidon_le {N : ℕ} {A : Finset ℕ} (hA : IsMaximalSidonSet N A) :
    minMaximalSidon N ≤ A.card :=
  Nat.sInf_le ⟨A, hA, rfl⟩

/-- The minimum is attained by a maximal Sidon set (PROVED in Lean). -/
theorem erdos_problem_156.exists_min (N : ℕ) :
    ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧ A.card = minMaximalSidon N := by
  obtain ⟨A, hA⟩ := erdos_problem_156.exists_maximal N
  exact Nat.sInf_mem (s := {k : ℕ | ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧ A.card = k})
    ⟨_, A, hA, rfl⟩

/-- A value `k` is the minimum if some maximal Sidon set has `k` elements and none has fewer (PROVED in Lean). -/
theorem erdos_problem_156.minMaximalSidon_eq {N k : ℕ}
    (hex : ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧ A.card = k)
    (hlow : ∀ A : Finset ℕ, IsMaximalSidonSet N A → k ≤ A.card) : minMaximalSidon N = k := by
  obtain ⟨A, hA, hc⟩ := hex
  exact le_antisymm (hc ▸ erdos_problem_156.minMaximalSidon_le hA)
    (by obtain ⟨B, hB, hBc⟩ := erdos_problem_156.exists_min N; rw [← hBc]; exact hlow B hB)

/-- The main statement is `minMaximalSidon N = O(N^(1/3))`, upstream's form (PROVED in Lean). -/
theorem erdos_problem_156.variants.main_iff_min :
    (∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧
        (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3)) ↔
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (minMaximalSidon N : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  constructor
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with N ⟨A, hA, hle⟩
    exact le_trans (by exact_mod_cast erdos_problem_156.minMaximalSidon_le hA) hle
  · rintro ⟨C, hC, h⟩
    refine ⟨C, hC, ?_⟩
    filter_upwards [h] with N hN
    obtain ⟨A, hA, hc⟩ := erdos_problem_156.exists_min N
    exact ⟨A, hA, by rw [hc]; exact hN⟩

/-- Every element of `{0, …, N - 1} \ A` of a maximal Sidon set `A` is `c + d - a` or `(c + d) / 2` for some
`a, c, d ∈ A`, so `N ≤ |A| + |A|² + |A|³` (PROVED in Lean). -/
theorem erdos_problem_156.variants.card_bound {N : ℕ} {A : Finset ℕ} (hA : IsMaximalSidonSet N A) :
    N ≤ A.card + A.card ^ 2 + A.card ^ 3 := by
  obtain ⟨hsub, hS, hmax⟩ := hA
  have hcov : Finset.range N \ A ⊆
      ((A ×ˢ (A ×ˢ A)).image (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2 - p.1)) ∪
        ((A ×ˢ A).image (fun p : ℕ × ℕ => (p.1 + p.2) / 2)) := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    by_contra hxT
    apply hmax x hx.1 hx.2
    apply erdos_problem_156.sidon_insert hS hx.2
    · intro c hc d hd h
      apply hxT
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(c, d), Finset.mem_product.mpr ⟨hc, hd⟩, by simp only; omega⟩)
    · intro a ha c hc d hd h
      apply hxT
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(a, c, d), Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hc, hd⟩⟩,
          by simp only; omega⟩)
  have hcard : (Finset.range N \ A).card ≤ A.card ^ 3 + A.card ^ 2 := by
    calc (Finset.range N \ A).card
        ≤ (((A ×ˢ (A ×ˢ A)).image (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2 - p.1)) ∪
          ((A ×ˢ A).image (fun p : ℕ × ℕ => (p.1 + p.2) / 2))).card := Finset.card_le_card hcov
      _ ≤ ((A ×ˢ (A ×ˢ A)).image (fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2 - p.1)).card +
          ((A ×ˢ A).image (fun p : ℕ × ℕ => (p.1 + p.2) / 2)).card := Finset.card_union_le _ _
      _ ≤ (A ×ˢ (A ×ˢ A)).card + (A ×ˢ A).card :=
          add_le_add Finset.card_image_le Finset.card_image_le
      _ = A.card ^ 3 + A.card ^ 2 := by
          rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
          ring
  have hN : (Finset.range N \ A).card + A.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hsub]; simp
  omega

/-- Every maximal Sidon set in `{0, …, N - 1}` has `N^(1/3) ≤ 2 |A|` (PROVED in Lean). -/
theorem erdos_problem_156.variants.lower_bound_pow {N : ℕ} {A : Finset ℕ}
    (hA : IsMaximalSidonSet N A) : (N : ℝ) ^ ((1 : ℝ) / 3) ≤ 2 * (A.card : ℝ) := by
  have h := erdos_problem_156.variants.card_bound hA
  rcases Nat.eq_zero_or_pos A.card with hk | hk
  · rw [hk] at h
    have : N = 0 := by simpa using h
    subst this
    simp [hk]
  · have h1 : A.card ≤ A.card ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : A.card ^ 2 ≤ A.card ^ 3 := Nat.pow_le_pow_right hk (by norm_num)
    have h8 : (N : ℝ) ≤ (2 * (A.card : ℝ)) ^ 3 := by
      have h' : N ≤ 8 * A.card ^ 3 := by omega
      calc (N : ℝ) ≤ ((8 * A.card ^ 3 : ℕ) : ℝ) := by exact_mod_cast h'
        _ = (2 * (A.card : ℝ)) ^ 3 := by push_cast; ring
    calc (N : ℝ) ^ ((1 : ℝ) / 3) ≤ ((2 * (A.card : ℝ)) ^ 3) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (Nat.cast_nonneg N) h8 (by norm_num)
      _ = 2 * (A.card : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num

/-- The page's easy lower bound, for every maximal Sidon set (PROVED in Lean): `|A| ≥ N^(1/3) / 2`. -/
theorem erdos_problem_156.variants.lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) (A : Finset ℕ), IsMaximalSidonSet N A →
      c * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ A.card := by
  refine ⟨1 / 2, by norm_num, fun N A hA => ?_⟩
  have := erdos_problem_156.variants.lower_bound_pow hA
  linarith

/-- Ruzsa's construction [Ru98b] (SOLVED in the literature, not proved here): for all large `N` there is a maximal Sidon
set in `{0, …, N - 1}` with at most `C * (N * log N)^(1/3)` elements. -/
theorem erdos_problem_156.variants.ruzsa_upper :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧
        (A.card : ℝ) ≤ C * ((N : ℝ) * Real.log (N : ℝ)) ^ ((1 : ℝ) / 3) :=
  sorry

/-- A maximal Sidon set need not be of maximum size: in `{0, …, 6}` both `{1, 2, 5}` and `{0, 1, 4, 6}` are maximal
(PROVED in Lean). -/
theorem erdos_problem_156.variants.maximal_not_maximum :
    IsMaximalSidonSet 7 {1, 2, 5} ∧ IsMaximalSidonSet 7 {0, 1, 4, 6} := by decide

/-- The least size of a maximal Sidon subset of `{0, …, 4}` is `3` (PROVED in Lean). -/
theorem erdos_problem_156.variants.minMaximalSidon_five : minMaximalSidon 5 = 3 := by
  refine erdos_problem_156.minMaximalSidon_eq ⟨{0, 1, 3}, by decide, by decide⟩ ?_
  have : ∀ A ∈ (Finset.range 5).powerset, IsMaximalSidonSet 5 A → 3 ≤ A.card := by decide
  exact fun A hA => this A (Finset.mem_powerset.mpr hA.1) hA

set_option maxRecDepth 100000 in
/-- The least size of a maximal Sidon subset of `{0, …, 6}` is `3` (PROVED in Lean, by evaluating the definition in the
kernel). -/
theorem erdos_problem_156.variants.minMaximalSidon_seven : minMaximalSidon 7 = 3 := by
  refine erdos_problem_156.minMaximalSidon_eq ⟨{1, 2, 5}, by decide, by decide⟩ ?_
  have : ∀ A ∈ (Finset.range 7).powerset, IsMaximalSidonSet 7 A → 3 ≤ A.card := by
    decide +kernel
  exact fun A hA => this A (Finset.mem_powerset.mpr hA.1) hA

end
