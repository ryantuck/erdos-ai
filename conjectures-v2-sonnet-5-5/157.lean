-- [AI - Claude Sonnet 5.5]: Erdős Problem 157 — second-pass formalization
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Group.Pointwise.Set.Basic

open Filter Set

noncomputable section

/-!
# Erdős Problem #157: An infinite Sidon set that is an asymptotic basis of order 3

*Source:* [erdosproblems.com/157](https://www.erdosproblems.com/157) (banner **PROVED**: "This has been solved in the
affirmative."; captured 2026-02-20 as the page and as the tidied problem box, with identical content; the page shows no
edit date, "Formalised statement? No" and 0 comments). [ESS94][Er94b]

Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

Remark recorded on the page: Yes, as shown by Pilatte [Pi23].

Tags: sidon sets.

**Status.** PROVED, answered YES by Pilatte in 2023 [Pi23]. The mirror (`teorth/erdosproblems`, `b916d95`) has `proved`
since 2025-08-31, no prize, formalised `no`; upstream (`df3f12d`) has no `157.lean`. **DEFERRED:** Pilatte's proof was not
seen. The `sorry` of the main theorem stands for his theorem, and the file's statement is the true direction.

**Encoding.**
* `IsInfiniteSidonSet A` says that `A ⊆ ℕ` is infinite and every sum `a + b` with `a, b ∈ A` determines the pair `{a, b}`,
  as in Problems 152–156.
* `IsAsymptoticBasisOrder3 A` says that every sufficiently large `n` is a sum `a + b + c` of three elements of `A`, with
  repetition allowed, that is, the 3-fold sumset of `A` is cofinite. `variants.basis_iff_add` proves that this is
  "`n ∈ A + A + A` for all large `n`" for the pointwise sum of sets.
* The statement says that some `A ⊆ ℕ` is both. The page's sets are sets of natural numbers, and `A ⊆ ℕ` here may contain
  `0`. Translating by `1` preserves both properties, so this changes nothing: `variants.positive_version` proves in Lean
  that the statement is equivalent to the same statement for sets of positive integers.
* The conjunct `Set.Infinite A` is redundant: a set of which every large number is a sum of three elements is infinite
  (`infinite_of_basis`, `variants.infinite_redundant`).
* Background, not formalized: a Sidon set cannot be an asymptotic basis of order 2, since it has at most about `√N`
  elements up to `N` and so at most about `N / 2` distinct sums `a + b ≤ N`. Order 3 is therefore the first order for which
  the question is meaningful.
* The theorem asserts the existence, which is the answer YES recorded on the page.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From the
  `/latex/156` fetch in the session logs, the site's bibliography for another problem.)
* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial geometry_. Math. Pannon. (1994),
  261–269. (From the `/latex/106` and `/latex/755` fetches in the session logs.)
* [Pi23] Pilatte, C. (2023), the paper that solves the problem. **DEFERRED:** only the key and "Pilatte's solution paper
  (2023)" were recovered, from a fetch of the page; the title and venue were not in any fetch, and neither was a
  `/latex/157` bibliography.
-/

/-- An infinite set A ⊆ ℕ is a Sidon set (B₂ set) if all pairwise sums
    are distinct: whenever a + b = c + d with a, b, c, d ∈ A, then
    {a, b} = {c, d} as multisets (i.e. either a = c and b = d, or a = d and b = c). -/
def IsInfiniteSidonSet (A : Set ℕ) : Prop :=
  Set.Infinite A ∧
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A set A ⊆ ℕ is an asymptotic basis of order 3 if every sufficiently
    large natural number can be represented as a sum of (exactly) 3 elements
    (with repetition allowed) from A. -/
def IsAsymptoticBasisOrder3 (A : Set ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, n = a + b + c

/--
Erdős Problem #157 [ESS94, Er94b] (PROVED, answer YES [Pi23]; the `sorry` stands for Pilatte's theorem):

Does there exist an infinite Sidon set which is an asymptotic basis of order 3?

A set A ⊆ ℕ is a Sidon set if all pairwise sums a + b (a, b ∈ A) are distinct.
A set A is an asymptotic basis of order 3 if every sufficiently large integer
is the sum of 3 elements from A.

Answered YES by Pilatte [Pi23].

Formalized as: there exists an infinite set A ⊆ ℕ that is a Sidon set and
an asymptotic basis of order 3.
-/
theorem erdos_problem_157 :
    ∃ A : Set ℕ, IsInfiniteSidonSet A ∧ IsAsymptoticBasisOrder3 A :=
  sorry

/-- A set of which every large number is a sum of three elements is infinite (PROVED in Lean). -/
theorem erdos_problem_157.infinite_of_basis {A : Set ℕ} (h : IsAsymptoticBasisOrder3 A) :
    A.Infinite := by
  intro hfin
  obtain ⟨M, hM⟩ := Set.Finite.bddAbove hfin
  unfold IsAsymptoticBasisOrder3 at h
  rw [Filter.eventually_atTop] at h
  obtain ⟨N, hN⟩ := h
  obtain ⟨a, ha, b, hb, c, hc, hn⟩ := hN (N + 3 * M + 1) (by omega)
  have h1 := hM ha
  have h2 := hM hb
  have h3 := hM hc
  omega

/-- The conjunct `Set.Infinite A` is redundant: the statement is equivalent to the one for a Sidon set that is an
asymptotic basis of order 3 (PROVED in Lean). -/
theorem erdos_problem_157.variants.infinite_redundant :
    (∃ A : Set ℕ, IsInfiniteSidonSet A ∧ IsAsymptoticBasisOrder3 A) ↔
    ∃ A : Set ℕ, (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
      a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)) ∧ IsAsymptoticBasisOrder3 A := by
  constructor
  · rintro ⟨A, ⟨-, hS⟩, hB⟩
    exact ⟨A, hS, hB⟩
  · rintro ⟨A, hS, hB⟩
    exact ⟨A, ⟨erdos_problem_157.infinite_of_basis hB, hS⟩, hB⟩

/-- Allowing `0 ∈ A` changes nothing: translating a solution by `1` gives a solution of positive integers (PROVED in
Lean). -/
theorem erdos_problem_157.variants.positive_version :
    (∃ A : Set ℕ, IsInfiniteSidonSet A ∧ IsAsymptoticBasisOrder3 A) ↔
    ∃ A : Set ℕ, (∀ a ∈ A, 1 ≤ a) ∧ IsInfiniteSidonSet A ∧ IsAsymptoticBasisOrder3 A := by
  constructor
  · rintro ⟨A, ⟨hinf, hS⟩, hB⟩
    refine ⟨(· + 1) '' A, ?_,
      ⟨hinf.image (fun x _ y _ h => by have h' : x + 1 = y + 1 := h; omega), ?_⟩, ?_⟩
    · rintro _ ⟨a, _, rfl⟩
      show 1 ≤ a + 1
      omega
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ h
      have h' : a + 1 + (b + 1) = c + 1 + (d + 1) := h
      rcases hS a ha b hb c hc d hd (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; subst h1; subst h2; exact ⟨rfl, rfl⟩
      · right; subst h1; subst h2; exact ⟨rfl, rfl⟩
    · unfold IsAsymptoticBasisOrder3 at hB ⊢
      rw [Filter.eventually_atTop] at hB ⊢
      obtain ⟨N, hN⟩ := hB
      refine ⟨N + 3, fun n hn => ?_⟩
      obtain ⟨a, ha, b, hb, c, hc, h⟩ := hN (n - 3) (by omega)
      exact ⟨a + 1, ⟨a, ha, rfl⟩, b + 1, ⟨b, hb, rfl⟩, c + 1, ⟨c, hc, rfl⟩, by omega⟩
  · rintro ⟨A, -, h⟩
    exact ⟨A, h⟩

open scoped Pointwise in
/-- `IsAsymptoticBasisOrder3 A` is "`n ∈ A + A + A` for all large `n`" for the pointwise sum of sets (PROVED in Lean). -/
theorem erdos_problem_157.variants.basis_iff_add (A : Set ℕ) :
    IsAsymptoticBasisOrder3 A ↔ ∀ᶠ n : ℕ in atTop, n ∈ A + A + A := by
  unfold IsAsymptoticBasisOrder3
  refine eventually_congr (Eventually.of_forall fun n => ?_)
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    exact Set.add_mem_add (Set.add_mem_add ha hb) hc
  · intro h
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_add.mp h
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
    exact ⟨a, ha, b, hb, c, hc, rfl⟩

end
