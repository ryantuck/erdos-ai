import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Filter Topology Real Finset BigOperators Classical

noncomputable section

/--
Erdős Problem #489 [Er61]:

Let A ⊆ ℕ be a set such that |A ∩ [1,x]| = o(x^{1/2}). Let
  B = { n ≥ 1 : a ∤ n for all a ∈ A }.
If B = {b₁ < b₂ < ⋯} then is it true that
  lim_{x→∞} (1/x) ∑_{b_i < x} (b_{i+1} - b_i)²
exists (and is finite)?

For example, when A = {p² : p prime} then B is the set of squarefree numbers,
and the existence of this limit was proved by Erdős.
-/
theorem erdos_problem_489
    (A : Set ℕ)
    (hA : Tendsto (fun x : ℕ =>
      (((Icc 1 x).filter (· ∈ A)).card : ℝ) / (x : ℝ) ^ ((1 : ℝ) / 2))
      atTop (nhds 0))
    (b : ℕ → ℕ)
    (hb_mono : StrictMono b)
    (hb_mem : ∀ n, 0 < b n ∧ ∀ a ∈ A, ¬(a ∣ b n))
    (hb_surj : ∀ m, 0 < m → (∀ a ∈ A, ¬(a ∣ m)) → ∃ n, b n = m) :
    ∃ L : ℝ, Tendsto
      (fun x : ℕ =>
        (∑ i ∈ (range x).filter (fun i => b i < x),
          ((b (i + 1) - b i : ℕ) : ℝ) ^ 2) / (x : ℝ))
      atTop (nhds L) :=
  sorry

end
