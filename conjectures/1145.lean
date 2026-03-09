import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Pointwise Filter Topology

noncomputable section

/--
The representation function for sets A, B ⊆ ℕ, counting the number of ways
to write n as a + b with a ∈ A and b ∈ B.
-/
def repFunction₂ (A B : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ B ∧ p.1 + p.2 = n}

/--
Erdős Problem #1145 [Va99, 1.17]:

A conjecture of Erdős and Sárközy. Let A = {1 ≤ a₁ < a₂ < ⋯} and
B = {1 ≤ b₁ < b₂ < ⋯} be infinite sets of positive integers with
aₙ / bₙ → 1 as n → ∞.

If A + B contains all sufficiently large positive integers, then
limsup 1_A ∗ 1_B(n) = ∞, i.e., the representation function is unbounded.

This is a stronger form of Erdős Problem #28. See also #331.
-/
theorem erdos_problem_1145 (A B : Set ℕ)
    (hA : A.Infinite)
    (hB : B.Infinite)
    (hAsymp : Tendsto (fun n => (↑(Nat.nth (· ∈ A) n) : ℝ) / (↑(Nat.nth (· ∈ B) n) : ℝ)) atTop (nhds 1))
    (hBasis : {n : ℕ | n ∉ (A + B)}.Finite) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction₂ A B n ≥ M :=
  sorry

end
