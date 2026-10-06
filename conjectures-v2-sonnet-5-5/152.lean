-- [AI - Claude Sonnet 5.5]: Erdős Problem 152 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

/-!
# Erdős Problem #152: Isolated points in the sumset of a Sidon set

*Source:* [erdosproblems.com/152](https://www.erdosproblems.com/152) (banner **OPEN** at capture: "This is open, and
cannot be resolved with a finite computation."; captured 2026-03-05 as the page and as the tidied problem box, with
identical content; the page shows no edit date and "Formalised statement? Yes"). [ESS94]

For any $M\geq 1$, if $A\subset \mathbb{N}$ is a sufficiently large finite Sidon set then there are at least $M$ many
$a\in A+A$ such that $a+1,a-1\not\in A+A$.

Remarks recorded on the page:
* There may even be $\gg \lvert A\rvert^2$ many such $a$.
* A similar question can be asked for truncations of infinite Sidon sets.

Tags: sidon sets. 0 comments at capture.

**Status.** OPEN on the captured page (2026-03-05). The status has changed since: the mirror (`teorth/erdosproblems`,
`b916d95`) has `proved` (informal status, 2026-04-03) and `proved (Lean)` (2026-08-23), no prize, and upstream's
`152.lean` (`df3f12d`) has the problem as `research solved`, with formal proofs by DeepMind's prover agent [DM26a], and
the quadratic variant also solved [DM26b]. **DEFERRED:** these proofs, who proved it, and the new text of the page
were not seen. The `sorry` of the main theorem therefore stands for a theorem that has since been proved, and the
file's statement is the true direction.

**Encoding.**
* `IsSidonSet A` says that every sum `a + b` with `a, b ∈ A` determines the pair `{a, b}`.
* `sumset A` is `A + A`, including the sums `a + a`; `variants.sumset_eq_add` proves that it is Mathlib's pointwise sum.
* `isIsolatedIn a S` says `a + 1 ∉ S` and (`a = 0` or `a - 1 ∉ S`). For `a = 0` the left neighbour is `-1`, which is not
  a natural number and is not a sum, so the clause is true; subtraction in `ℕ` would instead test `0 ∉ S`, which is
  the wrong condition. `variants.count_zero_five` checks the boundary. The count is translation invariant, so it does
  not matter whether `ℕ` includes `0`.
* The statement says: for every `M` there is `N` such that every Sidon set with at least `N` elements has at least `M`
  isolated points in its sumset. That is "$f(n)\to\infty$" for `f n` the least number of isolated points over Sidon sets
  of size `n`, which is how upstream states it.
* `variants.isolated_le_sq` proves that the number of isolated points is at most $\lvert A\rvert^2$, so the quadratic
  variant is the largest possible order. `variants.quadratic` is the page's "$\gg\lvert A\rvert^2$", and
  `variants.main_of_quadratic` proves in Lean that it implies the main theorem.
* `variants.sidon_zero_one_three`, `count_zero_one_three`, `count_seven`, `count_zero_one` and `count_zero_five` evaluate
  the encoding on concrete sets by `decide`. An exact search over all Sidon sets of size `n` with `min A = 0` and `max A ≤ 80`
  (`≤ 90` for `n = 5` and `n = 8`) gives `f n = 1, 0, 1, 2, 2, 3, 5, 5` for `n = 1, …, 8`, within that range.
* The second remark, on truncations of infinite Sidon sets, is not formalized. **DEFERRED:** its precise meaning (the
  truncations of an infinite Sidon set are finite Sidon sets of growing size, so the isolated points of their sumsets
  are covered by the main theorem; a question about the sumset of the infinite set is a different one). Upstream also
  leaves this as a TODO.

## References

* [ESS94] Erdős, P., Sárközy, A. and Sós, T., _On sum sets of Sidon sets, I_. J. Number Theory (1994), 329–347. (From
  upstream's docstring. **DEFERRED:** there is no `/latex/152` fetch in the session logs, so the page's own
  bibliography was not seen.)
* [DM26a], [DM26b] DeepMind prover agent, formal proofs of the problem and of the quadratic variant (2026), as linked by
  upstream's docstring. **DEFERRED:** not examined here.
-/

/--
A finite set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are
distinct: whenever a + b = c + d with a, b, c, d ∈ A, then
{a, b} = {c, d}.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
The sumset A + A of a finite set A ⊆ ℕ.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
An element n is **isolated** in a set S ⊆ ℕ if neither n - 1 nor n + 1
belongs to S.
-/
def isIsolatedIn (n : ℕ) (S : Finset ℕ) : Bool :=
  (n + 1 ∉ S) && (n = 0 || n - 1 ∉ S)

/--
Erdős Problem #152 [ESS94] (OPEN at capture, since proved, see the module docstring):

For any M ≥ 1, if A ⊆ ℕ is a sufficiently large finite Sidon set then there
are at least M elements a ∈ A + A such that a + 1 ∉ A + A and a - 1 ∉ A + A
(i.e., at least M isolated points in the sumset).
-/
theorem erdos_problem_152 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ (A : Finset ℕ),
      IsSidonSet A →
      N ≤ A.card →
      M ≤ ((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card :=
  sorry

open scoped Pointwise in
/-- `sumset A` is Mathlib's pointwise sum `A + A` of finsets (PROVED in Lean). -/
theorem erdos_problem_152.variants.sumset_eq_add (A : Finset ℕ) : sumset A = A + A := by
  unfold sumset
  exact Finset.image_add_product

/-- Being a Sidon set is decidable (used to evaluate the examples below by `decide`). -/
instance (A : Finset ℕ) : Decidable (IsSidonSet A) := by
  unfold IsSidonSet; infer_instance

/-- The number of isolated points of `A + A` is at most `|A| ^ 2` (PROVED in Lean), so the quadratic variant is the
largest possible order. -/
theorem erdos_problem_152.variants.isolated_le_sq (A : Finset ℕ) :
    ((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card ≤ A.card ^ 2 := by
  calc ((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card ≤ (sumset A).card :=
        Finset.card_filter_le _ _
    _ ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = A.card ^ 2 := by rw [Finset.card_product, pow_two]

/--
The page's remark "there may even be $\gg \lvert A\rvert^2$ many such $a$": there are `c > 0` and `N` such that every
Sidon set with at least `N` elements has at least `c * |A| ^ 2` isolated points in its sumset. At capture this was
open. Upstream records it as solved by DeepMind's prover agent [DM26b]. **DEFERRED:** the proof was not seen.
-/
theorem erdos_problem_152.variants.quadratic :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (A : Finset ℕ), IsSidonSet A → N ≤ A.card →
      c * (A.card : ℝ) ^ 2 ≤
        (((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card : ℝ) :=
  sorry

/-- The quadratic variant implies the main theorem (PROVED in Lean). -/
theorem erdos_problem_152.variants.main_of_quadratic
    (h : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (A : Finset ℕ), IsSidonSet A → N ≤ A.card →
      c * (A.card : ℝ) ^ 2 ≤
        (((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card : ℝ)) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ (A : Finset ℕ),
      IsSidonSet A →
      N ≤ A.card →
      M ≤ ((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card := by
  obtain ⟨c, hc, N₀, hN₀⟩ := h
  intro M
  obtain ⟨K, hK⟩ := exists_nat_ge ((M : ℝ) / c)
  refine ⟨max N₀ (max 1 K), fun A hA hcard => ?_⟩
  have h1 := hN₀ A hA (le_trans (le_max_left _ _) hcard)
  have hn : (1 : ℝ) ≤ (A.card : ℝ) := by
    have : 1 ≤ A.card := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hcard
    exact_mod_cast this
  have hM : (M : ℝ) / c ≤ (A.card : ℝ) := by
    have : K ≤ A.card := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hcard
    calc (M : ℝ) / c ≤ K := hK
      _ ≤ (A.card : ℝ) := by exact_mod_cast this
  have h2 : (M : ℝ) ≤ c * (A.card : ℝ) := by
    rw [div_le_iff₀ hc] at hM
    linarith
  have h3 : c * (A.card : ℝ) ≤ c * (A.card : ℝ) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    nlinarith
  exact_mod_cast (le_trans h2 (le_trans h3 h1))

/-- `{0, 1, 3}` is a Sidon set (PROVED in Lean, by `decide`). -/
theorem erdos_problem_152.variants.sidon_zero_one_three : IsSidonSet {0, 1, 3} := by decide

/-- `{0, 1, 3}` has sumset `{0, 1, 2, 3, 4, 6}` and one isolated point, `6` (PROVED in Lean, by `decide`). -/
theorem erdos_problem_152.variants.count_zero_one_three :
    ((sumset {0, 1, 3}).filter (fun a => isIsolatedIn a (sumset {0, 1, 3}))).card = 1 := by
  decide

/-- A Sidon set with seven elements and only five isolated points in its sumset (PROVED in Lean, by `decide`). By an
exact search this is the least possible for seven elements with `max A ≤ 80`. -/
theorem erdos_problem_152.variants.count_seven :
    IsSidonSet {0, 1, 4, 9, 15, 22, 34} ∧
      ((sumset {0, 1, 4, 9, 15, 22, 34}).filter
        (fun a => isIsolatedIn a (sumset {0, 1, 4, 9, 15, 22, 34}))).card = 5 := by
  decide

/-- `{0, 1}` has no isolated point (PROVED in Lean, by `decide`), so "sufficiently large" is needed for `M = 1`. -/
theorem erdos_problem_152.variants.count_zero_one :
    ((sumset {0, 1}).filter (fun a => isIsolatedIn a (sumset {0, 1}))).card = 0 := by
  decide

/-- The boundary: in `{0, 5} + {0, 5} = {0, 5, 10}` all three sums are isolated, including `0`, whose left neighbour `-1`
is not a sum (PROVED in Lean, by `decide`). -/
theorem erdos_problem_152.variants.count_zero_five :
    ((sumset {0, 5}).filter (fun a => isIsolatedIn a (sumset {0, 5}))).card = 3 := by
  decide
