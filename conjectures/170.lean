import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open Finset Filter

/-!
# Erdős Problem #170

The Sparse Ruler problem. Let F(N) be the smallest possible size of a subset
A ⊂ {0, 1, ..., N} such that every element of {0, 1, ..., N} can be written
as a difference of two elements of A (i.e., {0, ..., N} ⊂ A - A).

Find the value of lim_{N → ∞} F(N) / N^{1/2}.

Erdős and Gál [ErGa48] proved this limit exists. It is known to lie in the
interval [1.56, √3]. The lower bound is due to Leech [Le56], the upper bound
to Wichmann [Wi63]. Computational evidence by Pegg [Pe20] suggests √3 is the
true value.
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

/--
Erdős Problem #170 (Sparse Ruler conjecture) [ErGa48]:

The limit lim_{N → ∞} F(N) / √N equals √3.
-/
theorem erdos_problem_170 :
    Tendsto (fun N => (sparseRulerNumber N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds (Real.sqrt 3)) :=
  sorry
