import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

/--
A natural number n is powerful if for every prime p dividing n, p² also divides n.
By convention, 1 is powerful (vacuously).
-/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

instance (n : ℕ) : Decidable (IsPowerful n) := by
  unfold IsPowerful; exact sorry

/--
The number of representations of n as a product of two powerful numbers,
i.e., the Dirichlet convolution (1_A * 1_A)(n) where A is the set of powerful numbers.
-/
noncomputable def powerfulPairCount (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).filter (fun a =>
    a ∣ n ∧ IsPowerful a ∧ IsPowerful (n / a))
  |>.card

/--
Erdős Problem #943 [Er76d]:

Let A be the set of powerful numbers (if p ∣ n then p² ∣ n). Is it true that
(1_A * 1_A)(n) = n^{o(1)} for every n?

That is, the number of ways to write n as a product of two powerful numbers
grows slower than any positive power of n.
-/
theorem erdos_problem_943 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, (powerfulPairCount n : ℝ) ≤ (n : ℝ) ^ ε :=
  sorry
