import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Classical Finset

noncomputable section

/--
A composite number u that divides n! + 1 for some natural number n.
By Wilson's theorem, every prime p divides (p-1)! + 1, so the interesting
question is about composite numbers with this property.
-/
def IsFactorialWilsonComposite (u : ℕ) : Prop :=
  1 < u ∧ ¬Nat.Prime u ∧ ∃ n : ℕ, u ∣ (n.factorial + 1)

/--
A(x) counts the number of composite u < x such that u ∣ (n! + 1) for some n.
The sequence of such u begins 25, 121, 169, 437, … (OEIS A256519).
-/
noncomputable def factorialWilsonCompositeCount (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun u => IsFactorialWilsonComposite u)).card

/--
Erdős Problem #1073 [HaSu02]:

Let A(x) count the number of composite u < x such that n! + 1 ≡ 0 (mod u)
for some n. Is it true that A(x) ≤ x^{o(1)}?

A question of Erdős raised in discussions with Hardy and Subbarao.
Wilson's theorem states that u is prime if and only if (u-1)! + 1 ≡ 0 (mod u),
so the conjecture asks whether the composite numbers with this divisibility
property are extremely sparse.

The condition A(x) ≤ x^{o(1)} means: for every ε > 0, A(x) ≤ x^ε for all
sufficiently large x.
-/
theorem erdos_problem_1073 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
        (factorialWilsonCompositeCount x : ℝ) ≤ (x : ℝ) ^ ε :=
  sorry

end
