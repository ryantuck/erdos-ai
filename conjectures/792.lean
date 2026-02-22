import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #792

Let f(n) be maximal such that in any A ⊂ ℤ with |A| = n there exists some
sum-free subset B ⊆ A with |B| ≥ f(n), so that there are no solutions to
a + b = c with a, b, c ∈ B. Estimate f(n).

Erdős [Er65] gave a simple proof that f(n) ≥ n/3. The best lower bound known is
f(n) ≥ n/3 + c log log n for some c > 0, due to Bedert [Be25b]. The best upper
bound known is f(n) ≤ n/3 + o(n), due to Eberhard, Green, and Manners [EGM14].

https://www.erdosproblems.com/792
-/

/-- A finset of integers is sum-free if for all a, b in the set, a + b is not
    in the set. -/
def IsSumFreeSet (B : Finset ℤ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B

/-- f(n) is the largest k such that every n-element subset of ℤ contains
    a sum-free subset of size at least k. -/
noncomputable def maxSumFreeSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ IsSumFreeSet B ∧ k ≤ B.card}

/--
Erdős Problem #792, Erdős's lower bound [Er65]:
f(n) ≥ n/3 for all n.
-/
theorem erdos_problem_792_erdos_lower (n : ℕ) :
    (maxSumFreeSize n : ℝ) ≥ n / 3 := sorry

/--
Erdős Problem #792, best known lower bound (Bedert [Be25b]):
There exists c > 0 such that f(n) ≥ n/3 + c · log(log(n)) for all
sufficiently large n.
-/
theorem erdos_problem_792_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≥ n / 3 + c * Real.log (Real.log n) := sorry

/--
Erdős Problem #792, best known upper bound (Eberhard–Green–Manners [EGM14]):
f(n) ≤ n/3 + o(n), i.e., for every ε > 0, f(n) ≤ (1/3 + ε) · n for all
sufficiently large n.
-/
theorem erdos_problem_792_upper :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxSumFreeSize n : ℝ) ≤ (1 / 3 + ε) * n := sorry

end
