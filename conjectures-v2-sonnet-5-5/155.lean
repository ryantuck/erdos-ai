-- [AI - Claude Sonnet 5.5]: Erdős Problem 155 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Order.Filter.AtTopBot.Archimedean

open Filter Finset

noncomputable section

/-!
# Erdős Problem #155: Does the largest Sidon subset grow by at most one over a window of length `k`?

*Source:* [erdosproblems.com/155](https://www.erdosproblems.com/155) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; captured 2026-03-05 as the page and as the tidied problem box, with identical
content; the page shows no edit date, "Formalised statement? Yes", 1 comment, not captured, and lists the OEIS
sequences A143824, A227590 and A003022, not fetched). [Er92c][ESS94][Er94b]

Let $F(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$. Is it true that for every $k\geq 1$ the
inequality
$$F(N+k)\leq F(N)+1$$
holds for all sufficiently large $N$? (The page's first-person plural is replaced here by neutral wording.)

Remark recorded on the page: This may even hold with $k\approx \epsilon N^{1/2}$.

Tags: additive combinatorics, sidon sets.

**Status.** OPEN. The mirror (`teorth/erdosproblems`, `b916d95`) has `open` since 2025-08-31, no prize, formalised `yes`
(2025-08-31); upstream's `155.lean` (`df3f12d`) has `erdos_155` as `research open`, in the form
`answer(sorry) ↔ ∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1` with
`F N = Finset.maxSidonSubsetCard (Finset.Icc 1 N)`, and the remark as a TODO.

**Encoding.**
* `IsSidonSet A` says that every sum `a + b` with `a, b ∈ A` determines the pair `{a, b}`, as in Problems 152–154.
* `maxSidon N` is the largest size of a Sidon subset of `range N = {0, …, N - 1}`, defined as upstream defines
  `maxSidonSubsetCard`. Being Sidon is invariant under translation, so this is the page's `F(N)` for `{1, …, N}`.
* The statement says: for every `k ≥ 1`, for all large `N`, every Sidon `A ⊆ range (N + k)` has `|A| ≤ |B| + 1` for some
  Sidon `B ⊆ range N`. `variants.main_iff` proves in Lean that this is exactly `maxSidon (N + k) ≤ maxSidon N + 1`.
* The asked direction ("yes") is asserted, since the problem is open and the page asks a yes/no question.
* `variants.k_one` proves the case `k = 1` for every `N`, `variants.k_two` the case `k = 2` for every `N ≥ 1` (it fails
  at `N = 0`), and `variants.add_le` proves the subadditive bound `F(N + k) ≤ F(N) + F(k)`. The model found no elementary
  argument for `k = 3`. The question is whether `F(k)` can be replaced by `1` for large `N`. "Sufficiently large" is
  needed for `k ≥ 3` (`variants.fails_k3`, `variants.fails_k6`).
* `golombLength n` is the least `m` such that `{0, …, m}` has a Sidon subset of size `n`, that is, the length of an
  optimal Golomb ruler with `n` marks (for `n ≥ 1`). `variants.main_iff_gaps` proves in Lean that the main statement is
  equivalent to: for every `k`, `golombLength (m + 1) + k ≤ golombLength (m + 2)` for all large `m`, that is, the differences
  of consecutive optimal Golomb ruler lengths tend to infinity.
* `variants.epsilon_sqrt` is one reading of the page's remark: some `ε > 0` works uniformly for all `1 ≤ k ≤ ε √N`.
  It is OPEN, and `variants.main_of_epsilon_sqrt` proves in Lean that it implies the main statement. Since
  `F(N) = N^{1/2} + O(N^{1/4})` (Erdős–Turán, Lindström; not formalized), `golombLength n` is of order `n²`, and the
  remark asks that every gap be at least a constant multiple of `n` (the average gap is about `2n`). A statement for
  every `ε > 0` would be false (by hand, not formalized): gaps of at least `ε n` for all large `n` give
  `golombLength n ≥ (ε / 2 - o(1)) n²`, which contradicts `golombLength n ~ n²` once `ε > 2`.
* `variants.maxSidon_one`, `maxSidon_two`, `maxSidon_three`, `maxSidon_four`, `maxSidon_six`, `maxSidon_seven` evaluate
  `F` for small `N` (by `decide`, in the kernel for the last two) and `variants.golombLength_two`, `golombLength_three`,
  `golombLength_four` deduce the optimal lengths `1, 3, 6`. Optimal lengths up to `n = 12` were computed outside Lean
  and are in the review.
* **DEFERRED:** the precise meaning of the remark. The page gives only "$k\approx \epsilon N^{1/2}$". The model reads "some
  `ε > 0`" and "`k ≤ ε √N`", the only reading of the quantifier that can be true. Upstream leaves the remark as a TODO.

## References

* [Er92c] Erdős, P., _Some of my forgotten problems in number theory_. Hardy-Ramanujan J. (1992), 34–50. (From the
  `/latex/708` and `/latex/710` fetches in the session logs, the site's bibliography for other problems.)
* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From the
  `/latex/156` fetch in the session logs; upstream's docstring agrees.)
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial geometry_. Math. Pannon. (1994),
  261–269. (From the `/latex/106` and `/latex/755` fetches in the session logs.)
* **DEFERRED:** there is no `/latex/155` fetch, so this problem's own bibliography (which of the three references
  contains the question, and with what wording) was not seen.
-/

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, then {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
Erdős Problem #155 [Er92c][ESS94][Er94b] (OPEN):

For every k ≥ 1, for all sufficiently large N, every Sidon subset of
{0, ..., N+k-1} has size at most one more than the largest Sidon subset
of {0, ..., N-1}.

Equivalently: F(N+k) ≤ F(N) + 1, where F(N) = max {|A| : A ⊆ {0,...,N-1}, A Sidon}.
-/
theorem erdos_problem_155 :
    ∀ k : ℕ, 1 ≤ k →
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + k) → IsSidonSet A →
          ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ A.card ≤ B.card + 1 :=
  sorry

/-- Being a Sidon set is decidable (used to define `maxSidon` and to evaluate the examples below). -/
instance (A : Finset ℕ) : Decidable (IsSidonSet A) := by
  unfold IsSidonSet; infer_instance

/-- `maxSidon N` is `F(N)`: the largest size of a Sidon subset of `{0, …, N - 1}`. By translation invariance of the
Sidon property it is the page's `F(N)` for `{1, …, N}`. -/
def maxSidon (N : ℕ) : ℕ :=
  (((Finset.range N).powerset).filter (fun A => IsSidonSet A)).sup Finset.card

/-- `golombLength n` is the least `m` such that `{0, …, m}` contains a Sidon set with `n` elements, that is (for
`n ≥ 1`) the length of an optimal Golomb ruler with `n` marks. -/
def golombLength (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ maxSidon (m + 1)}

/-- A subset of a Sidon set is a Sidon set (PROVED in Lean). -/
theorem erdos_problem_155.sidon_mono {A B : Finset ℕ} (hB : IsSidonSet B) (h : A ⊆ B) : IsSidonSet A :=
  fun a ha b hb c hc d hd => hB a (h ha) b (h hb) c (h hc) d (h hd)

/-- Every Sidon subset of `{0, …, N - 1}` has at most `maxSidon N` elements (PROVED in Lean). -/
theorem erdos_problem_155.card_le_maxSidon {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range N)
    (hS : IsSidonSet A) : A.card ≤ maxSidon N :=
  Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hA, hS⟩)

/-- The maximum `maxSidon N` is attained by a Sidon subset of `{0, …, N - 1}` (PROVED in Lean). -/
theorem erdos_problem_155.exists_max_sidon (N : ℕ) :
    ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ B.card = maxSidon N := by
  have hne : (((Finset.range N).powerset).filter (fun A => IsSidonSet A)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, fun a ha => absurd ha (by simp)⟩⟩
  obtain ⟨B, hB, hBeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hB
  exact ⟨B, hB.1, hB.2, hBeq.symm⟩

/-- `maxSidon 0 = 0` (PROVED in Lean). -/
theorem erdos_problem_155.maxSidon_zero : maxSidon 0 = 0 := by
  obtain ⟨B, hB, -, hc⟩ := erdos_problem_155.exists_max_sidon 0
  have : B = ∅ := Finset.subset_empty.mp (by simpa using hB)
  rw [← hc, this]; rfl

/-- `maxSidon N ≤ N` (PROVED in Lean). -/
theorem erdos_problem_155.maxSidon_le (N : ℕ) : maxSidon N ≤ N := by
  obtain ⟨B, hB, -, hc⟩ := erdos_problem_155.exists_max_sidon N
  rw [← hc]
  simpa using Finset.card_le_card hB

/-- `maxSidon` is monotone (PROVED in Lean). -/
theorem erdos_problem_155.maxSidon_mono {N M : ℕ} (h : N ≤ M) : maxSidon N ≤ maxSidon M := by
  obtain ⟨B, hB, hS, hc⟩ := erdos_problem_155.exists_max_sidon N
  rw [← hc]
  exact erdos_problem_155.card_le_maxSidon (hB.trans (Finset.range_mono h)) hS

/-- Shifting a Sidon set down by a common lower bound gives a Sidon set (PROVED in Lean). -/
theorem erdos_problem_155.sidon_shift_down {A : Finset ℕ} (hA : IsSidonSet A) (N : ℕ)
    (hN : ∀ x ∈ A, N ≤ x) : IsSidonSet (A.image (· - N)) := by
  intro a ha b hb c hc d hd h
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
  have h1 := hN a' ha'
  have h2 := hN b' hb'
  have h3 := hN c' hc'
  have h4 := hN d' hd'
  rcases hA a' ha' b' hb' c' hc' d' hd' (by omega) with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · left; subst e1; subst e2; exact ⟨rfl, rfl⟩
  · right; subst e1; subst e2; exact ⟨rfl, rfl⟩

/-- Adding an element larger than twice the maximum to a Sidon set keeps it Sidon (PROVED in Lean). -/
theorem erdos_problem_155.sidon_insert_large {A : Finset ℕ} {M : ℕ} (hA : IsSidonSet A)
    (hM : ∀ y ∈ A, y ≤ M) : IsSidonSet (insert (2 * M + 1) A) := by
  intro a ha b hb c hc d hd h
  have key : ∀ y, y ∈ insert (2 * M + 1) A → y = 2 * M + 1 ∨ (y ∈ A ∧ y ≤ M) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hM y h⟩
  rcases key a ha with rfl | ⟨ha, ha'⟩ <;> rcases key b hb with rfl | ⟨hb, hb'⟩ <;>
    rcases key c hc with rfl | ⟨hc, hc'⟩ <;> rcases key d hd with rfl | ⟨hd, hd'⟩ <;>
    first
    | omega
    | exact hA _ ha _ hb _ hc _ hd h

/-- For every `n` there is a Sidon set with exactly `n` elements (PROVED in Lean). -/
theorem erdos_problem_155.exists_sidon_card (n : ℕ) : ∃ A : Finset ℕ, IsSidonSet A ∧ A.card = n := by
  induction n with
  | zero => exact ⟨∅, fun a ha => absurd ha (by simp), by simp⟩
  | succ n ih =>
    obtain ⟨A, hA, hc⟩ := ih
    refine ⟨insert (2 * A.sup id + 1) A,
      erdos_problem_155.sidon_insert_large hA (fun y hy => Finset.le_sup (f := id) hy), ?_⟩
    rw [Finset.card_insert_of_notMem, hc]
    intro hmem
    have := Finset.le_sup (f := id) hmem
    simp only [id] at this
    omega

/-- `maxSidon` is unbounded (PROVED in Lean). -/
theorem erdos_problem_155.maxSidon_unbounded (n : ℕ) : ∃ N : ℕ, n ≤ maxSidon N := by
  obtain ⟨A, hA, hc⟩ := erdos_problem_155.exists_sidon_card n
  refine ⟨A.sup id + 1, ?_⟩
  have hsub : A ⊆ Finset.range (A.sup id + 1) := by
    intro y hy
    have := Finset.le_sup (f := id) hy
    simp only [id] at this
    exact Finset.mem_range.mpr (by omega)
  rw [← hc]
  exact erdos_problem_155.card_le_maxSidon hsub hA

/-- For `n ≥ 1`, `{0, …, N - 1}` has a Sidon subset of size `n` iff `golombLength n < N` (PROVED in Lean). -/
theorem erdos_problem_155.le_maxSidon_iff {n : ℕ} (hn : 1 ≤ n) (N : ℕ) :
    n ≤ maxSidon N ↔ golombLength n < N := by
  constructor
  · intro h
    cases N with
    | zero => rw [erdos_problem_155.maxSidon_zero] at h; omega
    | succ m =>
      have : golombLength n ≤ m := Nat.sInf_le (show m ∈ {m : ℕ | n ≤ maxSidon (m + 1)} from h)
      omega
  · intro h
    have hne : {m : ℕ | n ≤ maxSidon (m + 1)}.Nonempty := by
      obtain ⟨N, hN⟩ := erdos_problem_155.maxSidon_unbounded n
      exact ⟨N, hN.trans (erdos_problem_155.maxSidon_mono (Nat.le_succ N))⟩
    have hmem : n ≤ maxSidon (golombLength n + 1) := Nat.sInf_mem hne
    exact hmem.trans (erdos_problem_155.maxSidon_mono (by omega))

/-- `golombLength (m + 1) ≥ m` (PROVED in Lean). -/
theorem erdos_problem_155.golombLength_ge (m : ℕ) : m ≤ golombLength (m + 1) := by
  have h := (erdos_problem_155.le_maxSidon_iff (n := m + 1) (by omega) (golombLength (m + 1) + 1)).mpr
    (by omega)
  have := erdos_problem_155.maxSidon_le (golombLength (m + 1) + 1)
  omega

/--
The main theorem is the statement about `F` (PROVED in Lean): for every `k ≥ 1`, for all large `N`, the existence of the
set `B` for every Sidon `A ⊆ {0, …, N + k - 1}` is exactly `F(N + k) ≤ F(N) + 1`.
-/
theorem erdos_problem_155.variants.main_iff :
    (∀ k : ℕ, 1 ≤ k →
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + k) → IsSidonSet A →
          ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ A.card ≤ B.card + 1) ↔
    ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop, maxSidon (N + k) ≤ maxSidon N + 1 := by
  have key : ∀ k N : ℕ, (∀ A : Finset ℕ, A ⊆ Finset.range (N + k) → IsSidonSet A →
          ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ A.card ≤ B.card + 1) ↔
      maxSidon (N + k) ≤ maxSidon N + 1 := by
    intro k N
    constructor
    · intro h
      obtain ⟨A, hA, hS, hcard⟩ := erdos_problem_155.exists_max_sidon (N + k)
      obtain ⟨B, hB, hBS, hle⟩ := h A hA hS
      have := erdos_problem_155.card_le_maxSidon hB hBS
      omega
    · intro h A hA hS
      obtain ⟨B, hB, hBS, hcard⟩ := erdos_problem_155.exists_max_sidon N
      have := erdos_problem_155.card_le_maxSidon hA hS
      exact ⟨B, hB, hBS, by omega⟩
  constructor
  · intro h k hk
    filter_upwards [h k hk] with N hN
    exact (key k N).mp hN
  · intro h k hk
    filter_upwards [h k hk] with N hN
    exact (key k N).mpr hN

/-- A Sidon set with all elements in `[s, s + M)` has at most `maxSidon M` elements (PROVED in Lean). -/
theorem erdos_problem_155.card_le_maxSidon_shift {A : Finset ℕ} (hS : IsSidonSet A) (s M : ℕ)
    (hlo : ∀ x ∈ A, s ≤ x) (hhi : ∀ x ∈ A, x < s + M) : A.card ≤ maxSidon M := by
  have hinj : Set.InjOn (· - s) (A : Set ℕ) := by
    intro x hx y hy hxy
    have h1 := hlo x hx
    have h2 := hlo y hy
    simp only at hxy
    omega
  have hsub : A.image (· - s) ⊆ Finset.range M := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h1 := hhi x hx
    have h2 := hlo x hx
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.card_image_of_injOn hinj]
  exact erdos_problem_155.card_le_maxSidon hsub (erdos_problem_155.sidon_shift_down hS s hlo)

/-- The case `k = 1` holds for every `N`: `F(N + 1) ≤ F(N) + 1` (PROVED in Lean). -/
theorem erdos_problem_155.variants.k_one (N : ℕ) : maxSidon (N + 1) ≤ maxSidon N + 1 := by
  obtain ⟨A, hA, hS, hcard⟩ := erdos_problem_155.exists_max_sidon (N + 1)
  have hB : A.erase N ⊆ Finset.range N := by
    intro x hx
    rw [Finset.mem_erase] at hx
    have := Finset.mem_range.mp (hA hx.2)
    exact Finset.mem_range.mpr (by omega)
  have h1 := erdos_problem_155.card_le_maxSidon hB
    (erdos_problem_155.sidon_mono hS (Finset.erase_subset _ _))
  have h2 := Finset.pred_card_le_card_erase (s := A) (a := N)
  omega

/-- The case `k = 2` holds for every `N ≥ 1`: `F(N + 2) ≤ F(N) + 1` (PROVED in Lean). It fails at `N = 0`, where
`F(2) = 2 > 1`. -/
theorem erdos_problem_155.variants.k_two (N : ℕ) (hN : 1 ≤ N) : maxSidon (N + 2) ≤ maxSidon N + 1 := by
  obtain ⟨A, hA, hS, hcard⟩ := erdos_problem_155.exists_max_sidon (N + 2)
  have hlt : ∀ x ∈ A, x < N + 2 := fun x hx => Finset.mem_range.mp (hA hx)
  have hk1 := erdos_problem_155.variants.k_one N
  by_cases h1 : N + 1 ∈ A
  · by_cases h2 : N ∈ A
    · by_cases h0 : 0 ∈ A
      · have h01 : 1 ∉ A := by
          intro h
          have := hS 0 h0 (N + 1) h1 1 h N h2 (by omega)
          omega
        have hlo : ∀ x ∈ A.erase 0, 2 ≤ x := by
          intro x hx
          rw [Finset.mem_erase] at hx
          have : x ≠ 1 := fun h => h01 (h ▸ hx.2)
          omega
        have hhi : ∀ x ∈ A.erase 0, x < 2 + N := by
          intro x hx
          have := hlt x (Finset.mem_erase.mp hx).2
          omega
        have c1 := erdos_problem_155.card_le_maxSidon_shift
          (erdos_problem_155.sidon_mono hS (Finset.erase_subset _ _)) 2 N hlo hhi
        have c2 := Finset.pred_card_le_card_erase (s := A) (a := 0)
        omega
      · have hlo : ∀ x ∈ A, 1 ≤ x := by
          intro x hx
          have : x ≠ 0 := fun h => h0 (h ▸ hx)
          omega
        have hhi : ∀ x ∈ A, x < 1 + (N + 1) := by
          intro x hx
          have := hlt x hx
          omega
        have c1 := erdos_problem_155.card_le_maxSidon_shift hS 1 (N + 1) hlo hhi
        omega
    · have hB : A.erase (N + 1) ⊆ Finset.range N := by
        intro x hx
        rw [Finset.mem_erase] at hx
        have h3 := hlt x hx.2
        have : x ≠ N := fun h => h2 (h ▸ hx.2)
        exact Finset.mem_range.mpr (by omega)
      have c1 := erdos_problem_155.card_le_maxSidon hB
        (erdos_problem_155.sidon_mono hS (Finset.erase_subset _ _))
      have c2 := Finset.pred_card_le_card_erase (s := A) (a := N + 1)
      omega
  · have hB : A ⊆ Finset.range (N + 1) := by
      intro x hx
      have h3 := hlt x hx
      have : x ≠ N + 1 := fun h => h1 (h ▸ hx)
      exact Finset.mem_range.mpr (by omega)
    have c1 := erdos_problem_155.card_le_maxSidon hB hS
    omega

/-- `F` is subadditive: `F(N + k) ≤ F(N) + F(k)` for all `N` and `k` (PROVED in Lean). The question is whether `F(k)` can
be replaced by `1` once `N` is large. -/
theorem erdos_problem_155.variants.add_le (N k : ℕ) : maxSidon (N + k) ≤ maxSidon N + maxSidon k := by
  obtain ⟨A, hA, hS, hcard⟩ := erdos_problem_155.exists_max_sidon (N + k)
  have hlow : A.filter (· < N) ⊆ Finset.range N := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
  have hlowS : IsSidonSet (A.filter (· < N)) :=
    erdos_problem_155.sidon_mono hS (Finset.filter_subset _ _)
  have hhigh : ∀ x ∈ A.filter (fun x => ¬ x < N), N ≤ x := by
    intro x hx
    have := (Finset.mem_filter.mp hx).2
    omega
  have hhighS : IsSidonSet ((A.filter (fun x => ¬ x < N)).image (· - N)) :=
    erdos_problem_155.sidon_shift_down
      (erdos_problem_155.sidon_mono hS (Finset.filter_subset _ _)) N hhigh
  have hhighR : (A.filter (fun x => ¬ x < N)).image (· - N) ⊆ Finset.range k := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have h1 := Finset.mem_range.mp (hA (Finset.mem_filter.mp hx).1)
    have h2 := hhigh x hx
    exact Finset.mem_range.mpr (by omega)
  have hinj : Set.InjOn (· - N) (A.filter (fun x => ¬ x < N) : Set ℕ) := by
    intro x hx y hy hxy
    have h1 := hhigh x hx
    have h2 := hhigh y hy
    simp only at hxy
    omega
  have c1 := erdos_problem_155.card_le_maxSidon hlow hlowS
  have c2 := erdos_problem_155.card_le_maxSidon hhighR hhighS
  have c3 : ((A.filter (fun x => ¬ x < N)).image (· - N)).card =
      (A.filter (fun x => ¬ x < N)).card := Finset.card_image_of_injOn hinj
  have c4 := Finset.card_filter_add_card_filter_not (s := A) (fun x => x < N)
  omega

/--
The main statement is equivalent to a statement about optimal Golomb rulers (PROVED in Lean): for every `k ≥ 1`,
`F(N + k) ≤ F(N) + 1` for all large `N`, iff for every `k`, `L(m + 1) + k ≤ L(m + 2)` for all large `m`, where `L n`
is `golombLength n`. That is, the differences `L(m + 2) - L(m + 1)` of consecutive optimal lengths tend to infinity.
-/
theorem erdos_problem_155.variants.main_iff_gaps :
    (∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop, maxSidon (N + k) ≤ maxSidon N + 1) ↔
    ∀ k : ℕ, ∀ᶠ m : ℕ in atTop, golombLength (m + 1) + k ≤ golombLength (m + 2) := by
  constructor
  · intro h k
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (h (k + 1) (by omega))
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun m hm => ?_⟩
    have hge := erdos_problem_155.golombLength_ge m
    have h1 := hN₀ (golombLength (m + 1)) (by omega)
    have h2 : ¬ (m + 1 ≤ maxSidon (golombLength (m + 1))) := by
      rw [erdos_problem_155.le_maxSidon_iff (by omega)]; omega
    have h3 : ¬ (m + 2 ≤ maxSidon (golombLength (m + 1) + (k + 1))) := by
      intro h4
      omega
    rw [erdos_problem_155.le_maxSidon_iff (by omega)] at h3
    omega
  · intro h k hk
    obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (h k)
    obtain ⟨N₀, hN₀⟩ := erdos_problem_155.maxSidon_unbounded M₀
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun N hN => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hm : M₀ ≤ maxSidon N := hN₀.trans (erdos_problem_155.maxSidon_mono hN)
    have h1 := hM₀ (maxSidon N) hm
    have h2 : golombLength (maxSidon N + 2) < N + k :=
      (erdos_problem_155.le_maxSidon_iff (by omega) (N + k)).mp (by omega)
    have h3 : ¬ golombLength (maxSidon N + 1) < N := fun h =>
      by have := (erdos_problem_155.le_maxSidon_iff (by omega) N).mpr h; omega
    omega

/--
A reading of the page's remark "This may even hold with $k\approx \epsilon N^{1/2}$" (OPEN): there is `ε > 0` such that
for all large `N` and every `k` with `1 ≤ k ≤ ε √N`, `F(N + k) ≤ F(N) + 1`. Stated with `maxSidon`, which
`variants.main_iff` identifies with the main statement.
-/
theorem erdos_problem_155.variants.epsilon_sqrt :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ ε * Real.sqrt (N : ℝ) →
      maxSidon (N + k) ≤ maxSidon N + 1 :=
  sorry

/-- The remark's uniform statement implies the main statement (PROVED in Lean): for fixed `k`, eventually
`k ≤ ε √N`. -/
theorem erdos_problem_155.variants.main_of_epsilon_sqrt
    (h : ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ ε * Real.sqrt (N : ℝ) →
      maxSidon (N + k) ≤ maxSidon N + 1) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + k) → IsSidonSet A →
          ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ A.card ≤ B.card + 1 := by
  obtain ⟨ε, hε, h⟩ := h
  rw [erdos_problem_155.variants.main_iff]
  intro k hk
  have hlim : Tendsto (fun N : ℕ => ε * Real.sqrt (N : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  filter_upwards [h, hlim.eventually_ge_atTop (k : ℝ)] with N hN hNk
  exact hN k hk hNk

/-- `F(1) = 1` (PROVED in Lean). -/
theorem erdos_problem_155.variants.maxSidon_one : maxSidon 1 = 1 := by decide

/-- `F(2) = 2` (PROVED in Lean). -/
theorem erdos_problem_155.variants.maxSidon_two : maxSidon 2 = 2 := by decide

/-- `F(3) = 2`, since `{0, 1, 2}` is not Sidon (`0 + 2 = 1 + 1`) (PROVED in Lean). -/
theorem erdos_problem_155.variants.maxSidon_three : maxSidon 3 = 2 := by decide

/-- `F(4) = 3`, attained by `{0, 1, 3}` (PROVED in Lean). -/
theorem erdos_problem_155.variants.maxSidon_four : maxSidon 4 = 3 := by decide

set_option maxRecDepth 100000 in
/-- `F(6) = 3` (PROVED in Lean, by evaluating the definition in the kernel). -/
theorem erdos_problem_155.variants.maxSidon_six : maxSidon 6 = 3 := by decide +kernel

set_option maxRecDepth 100000 in
/-- `F(7) = 4`, attained by `{0, 1, 4, 6}` (PROVED in Lean, by evaluating the definition in the kernel). -/
theorem erdos_problem_155.variants.maxSidon_seven : maxSidon 7 = 4 := by decide +kernel

/-- The optimal Golomb ruler with two marks has length `1` (PROVED in Lean). -/
theorem erdos_problem_155.variants.golombLength_two : golombLength 2 = 1 := by
  have h1 := (erdos_problem_155.le_maxSidon_iff (n := 2) (by norm_num) 2).mp
    (by rw [erdos_problem_155.variants.maxSidon_two])
  have h2 : ¬ golombLength 2 < 1 := fun h => by
    have := (erdos_problem_155.le_maxSidon_iff (n := 2) (by norm_num) 1).mpr h
    rw [erdos_problem_155.variants.maxSidon_one] at this
    omega
  omega

/-- The optimal Golomb ruler with three marks has length `3` (PROVED in Lean). -/
theorem erdos_problem_155.variants.golombLength_three : golombLength 3 = 3 := by
  have h1 := (erdos_problem_155.le_maxSidon_iff (n := 3) (by norm_num) 4).mp
    (by rw [erdos_problem_155.variants.maxSidon_four])
  have h2 : ¬ golombLength 3 < 3 := fun h => by
    have := (erdos_problem_155.le_maxSidon_iff (n := 3) (by norm_num) 3).mpr h
    rw [erdos_problem_155.variants.maxSidon_three] at this
    omega
  omega

/-- The optimal Golomb ruler with four marks has length `6` (PROVED in Lean). -/
theorem erdos_problem_155.variants.golombLength_four : golombLength 4 = 6 := by
  have h1 := (erdos_problem_155.le_maxSidon_iff (n := 4) (by norm_num) 7).mp
    (by rw [erdos_problem_155.variants.maxSidon_seven])
  have h2 : ¬ golombLength 4 < 6 := fun h => by
    have := (erdos_problem_155.le_maxSidon_iff (n := 4) (by norm_num) 6).mpr h
    rw [erdos_problem_155.variants.maxSidon_six] at this
    omega
  omega

/-- "Sufficiently large" is needed for `k = 3`: `F(1 + 3) = 3 > 2 = F(1) + 1` (PROVED in Lean). -/
theorem erdos_problem_155.variants.fails_k3 : ¬ (maxSidon (1 + 3) ≤ maxSidon 1 + 1) := by
  have h1 := erdos_problem_155.variants.maxSidon_one
  have h4 : maxSidon (1 + 3) = 3 := erdos_problem_155.variants.maxSidon_four
  omega

/-- "Sufficiently large" is needed for `k = 6`: `F(6 + 6) ≥ 5 > 4 = F(6) + 1`, with `{0, 1, 4, 9, 11}` a Sidon subset of
`{0, …, 11}` (PROVED in Lean). -/
theorem erdos_problem_155.variants.fails_k6 : ¬ (maxSidon (6 + 6) ≤ maxSidon 6 + 1) := by
  have h6 := erdos_problem_155.variants.maxSidon_six
  have h12 : 5 ≤ maxSidon (6 + 6) := by
    have hS : IsSidonSet ({0, 1, 4, 9, 11} : Finset ℕ) := by decide
    exact erdos_problem_155.card_le_maxSidon (A := {0, 1, 4, 9, 11}) (by decide) hS
  omega

end
