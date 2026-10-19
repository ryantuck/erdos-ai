-- [AI - Claude Opus 5.5]: Erdős Problem 170 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

import Mathlib.Data.Finset.Powerset

open Finset Filter

/-!
# Erdős Problem #170 (the sparse ruler problem)

*Source:* [erdosproblems.com/170](https://www.erdosproblems.com/170) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-03-05; OEIS A046693). [ErGa48]

Let $F(N)$ be the smallest possible size of $A\subset \{0,1,\ldots,N\}$ such that
$\{0,1,\ldots,N\}\subset A-A$. Find the value of $\lim_{N\to \infty}\frac{F(N)}{N^{1/2}}$.

Remarks recorded on the page: the Sparse Ruler problem. Rédei asked whether this limit exists,
which was proved by Erdős and Gál [ErGa48]. Bounds on the limit were improved by Leech [Le56]. The
limit is known to be in the interval $[1.56,\sqrt{3}]$. The lower bound is due to Leech [Le56], the
upper bound is due to Wichmann [Wi63]. Computational evidence by Pegg [Pe20] suggests that the upper
bound is the truth. A similar question can be asked without the restriction
$A\subset \{0,1,\ldots,N\}$.

## Encoding notes

* The page asks for the value. The main theorem asserts the value that Pegg's computations [Pe20]
  suggest, $\sqrt3$ (Wichmann's upper bound). The known content is `variants.limit_exists` and
  `variants.bounds`.
* `IsDifferenceBasis N A` is `A ⊆ {0, …, N}` and `{0, …, N} ⊆ A - A`; `sparseRulerNumber N` is
  the least size of such an `A` (the set is nonempty by `differenceBasis_exists`). Values (PROVED
  by `decide`): `F 0, F 1, F 2, F 3, F 6, F 9 = 1, 2, 3, 3, 4, 5`, as in A046693. Counting
  differences gives `N ≤ (F N).choose 2` (PROVED), so `F N ≥ √(2N)` and any limit is at least
  `√2`.

## References

**DEFERRED:** no site bibliography entry was recovered for [ErGa48] (Erdős and Gál, 1948), [Le56]
(Leech, 1956), [Wi63] (Wichmann, 1963) or [Pe20] (Pegg, 2020).

*Provenance:* second pass of `conjectures/170.lean` (Opus 5.5 review, `opus-5-5-review/170.md`).
-/

/-- A subset A of {0, ..., N} is a difference basis for {0, ..., N} if every
    d ∈ {0, ..., N} can be written as b - a for some a, b ∈ A (with a ≤ b). -/
def IsDifferenceBasis (N : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, a ≤ N) ∧
    ∀ d : ℕ, d ≤ N → ∃ a ∈ A, ∃ b ∈ A, b = a + d

/-- There always exists a difference basis for {0, ..., N}, namely
    the full set {0, ..., N} itself. -/
lemma differenceBasis_exists (N : ℕ) :
    ∃ A : Finset ℕ, IsDifferenceBasis N A ∧ A.card > 0 := by
  exact ⟨Finset.range (N + 1), ⟨fun a ha => by simp [Finset.mem_range] at ha; omega,
    fun d hd => ⟨0, by simp, d, by simp [Finset.mem_range]; omega, by omega⟩⟩,
    by simp⟩

/-- F(N): the minimum size of a difference basis for {0, ..., N}. -/
noncomputable def sparseRulerNumber (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ IsDifferenceBasis N A}

/-- `IsDifferenceBasis N A` is decidable (a bounded check), for the `decide` proofs below. -/
instance erdos_problem_170.decIsDifferenceBasis (N : ℕ) (A : Finset ℕ) :
    Decidable (IsDifferenceBasis N A) := by
  unfold IsDifferenceBasis; infer_instance

/--
Erdős Problem #170 (Sparse Ruler conjecture) [ErGa48]:

The limit lim_{N → ∞} F(N) / √N equals √3.

(Status: OPEN. The page asks for the value of the limit; √3 is the value suggested by Pegg's
computations [Pe20], not a result of [ErGa48].)
-/
theorem erdos_problem_170 :
    Tendsto (fun N => (sparseRulerNumber N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds (Real.sqrt 3)) :=
  sorry

/-- To show `sparseRulerNumber N = m`, exhibit a basis with `m` marks and check all subsets of
`{0, …, N}` (PROVED in Lean). -/
theorem erdos_problem_170.sparseRulerNumber_eq_of (N m : ℕ) (A : Finset ℕ) (hA : IsDifferenceBasis N A)
    (hcard : A.card = m)
    (hmin : ∀ B ∈ (Finset.range (N + 1)).powerset, IsDifferenceBasis N B → m ≤ B.card) :
    sparseRulerNumber N = m := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨A, hcard, hA⟩
  · have hne : ({k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ IsDifferenceBasis N A}).Nonempty :=
      ⟨m, A, hcard, hA⟩
    obtain ⟨B, hB, hBb⟩ := Nat.sInf_mem hne
    unfold sparseRulerNumber
    rw [← hB]
    apply hmin B _ hBb
    rw [Finset.mem_powerset]
    intro b hb
    rw [Finset.mem_range]
    have := hBb.1 b hb
    omega

/-- `F 0 = 1`, `F 1 = 2`, `F 2 = 3`, `F 3 = 3` (PROVED by `decide`). -/
theorem erdos_problem_170.F_small : sparseRulerNumber 0 = 1 ∧ sparseRulerNumber 1 = 2 ∧ sparseRulerNumber 2 = 3 ∧
    sparseRulerNumber 3 = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact erdos_problem_170.sparseRulerNumber_eq_of 0 1 {0} (by decide) rfl (by decide)
  · exact erdos_problem_170.sparseRulerNumber_eq_of 1 2 {0, 1} (by decide) rfl (by decide)
  · exact erdos_problem_170.sparseRulerNumber_eq_of 2 3 {0, 1, 2} (by decide) rfl (by decide)
  · exact erdos_problem_170.sparseRulerNumber_eq_of 3 3 {0, 1, 3} (by decide) rfl (by decide)

/-- `F 6 = 4`, with the ruler `{0, 1, 4, 6}` (PROVED by kernel `decide`). -/
theorem erdos_problem_170.F_six : sparseRulerNumber 6 = 4 :=
  erdos_problem_170.sparseRulerNumber_eq_of 6 4 {0, 1, 4, 6} (by decide) rfl (by decide +kernel)

/-- `F 9 = 5`, with the ruler `{0, 1, 2, 6, 9}` (PROVED by kernel `decide`). -/
theorem erdos_problem_170.F_nine : sparseRulerNumber 9 = 5 :=
  erdos_problem_170.sparseRulerNumber_eq_of 9 5 {0, 1, 2, 6, 9} (by decide) rfl (by decide +kernel)

/-- A difference basis for `{0, …, N}` with `k` marks has `N ≤ k.choose 2`: each `d ∈ {1, …, N}`
is the difference of a pair of marks (PROVED in Lean). -/
theorem erdos_problem_170.le_choose_of_basis (N : ℕ) (A : Finset ℕ) (hA : IsDifferenceBasis N A) :
    N ≤ A.card.choose 2 := by
  classical
  let g : Finset ℕ → ℕ := fun s => s.sup id - (s.sum id - s.sup id)
  have hsub : Finset.Icc 1 N ⊆ (A.powersetCard 2).image g := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    obtain ⟨a, ha, b, hb, rfl⟩ := hA.2 d hd.2
    rw [Finset.mem_image]
    refine ⟨{a, a + d}, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hb
      · rw [Finset.card_pair (by omega)]
    · have hne : a ≠ a + d := by omega
      simp only [g, Finset.sup_insert, Finset.sup_singleton, id, Finset.sum_pair hne]
      have : a ⊔ (a + d) = a + d := by simp
      rw [this]
      omega
  calc N = (Finset.Icc 1 N).card := by simp
    _ ≤ ((A.powersetCard 2).image g).card := Finset.card_le_card hsub
    _ ≤ (A.powersetCard 2).card := Finset.card_image_le
    _ = A.card.choose 2 := Finset.card_powersetCard 2 A

/-- Hence `N ≤ (F N).choose 2`, so `F N ≥ √(2N)` (PROVED in Lean). -/
theorem erdos_problem_170.le_choose (N : ℕ) : N ≤ (sparseRulerNumber N).choose 2 := by
  obtain ⟨A, hA, -⟩ := differenceBasis_exists N
  have hmem : sparseRulerNumber N ∈ {k : ℕ | ∃ A : Finset ℕ, A.card = k ∧ IsDifferenceBasis N A} :=
    Nat.sInf_mem ⟨A.card, A, rfl, hA⟩
  obtain ⟨B, hB, hBb⟩ := hmem
  rw [← hB]
  exact erdos_problem_170.le_choose_of_basis N B hBb

/-- Erdős and Gál [ErGa48] (SOLVED; not proved here): the limit exists. -/
theorem erdos_problem_170.variants.limit_exists :
    ∃ L : ℝ, Tendsto (fun N => (sparseRulerNumber N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds L) :=
  sorry

/-- Leech [Le56] and Wichmann [Wi63] (SOLVED; not proved here): the limit lies in
$[1.56,\sqrt3]$. -/
theorem erdos_problem_170.variants.bounds :
    ∃ L : ℝ, 1.56 ≤ L ∧ L ≤ Real.sqrt 3 ∧
      Tendsto (fun N => (sparseRulerNumber N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds L) :=
  sorry
