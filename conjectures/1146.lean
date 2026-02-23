import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical

noncomputable section

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n
-/
noncomputable def schnirelmannDensity1146 (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The sumset A + B = {a + b | a ∈ A, b ∈ B} for sets of natural numbers.
-/
def sumset1146 (A B : Set ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/--
A set A ⊆ ℕ is an essential component if d_s(A + B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density.
-/
def IsEssentialComponent1146 (A : Set ℕ) : Prop :=
  ∀ (B : Set ℕ), 0 < schnirelmannDensity1146 B → schnirelmannDensity1146 B < 1 →
    schnirelmannDensity1146 (sumset1146 A B) > schnirelmannDensity1146 B

/--
The set of 3-smooth numbers: {2^m * 3^n | m, n ≥ 0}.
-/
def smoothNumbers23 : Set ℕ :=
  {k | ∃ m n : ℕ, k = 2 ^ m * 3 ^ n}

/--
Erdős Problem #1146 [Va99, 1.19]:
Is the set B = {2^m * 3^n : m, n ≥ 0} an essential component?

A set A ⊆ ℕ is an essential component if d_s(A + B) > d_s(B) for every
B ⊆ ℕ with 0 < d_s(B) < 1, where d_s is the Schnirelmann density.

Ruzsa states: "The simplest set with a chance to be an essential component is
the collection of numbers in the form 2^m * 3^n and Erdős often asked whether
it is an essential component or not."
-/
theorem erdos_problem_1146 : IsEssentialComponent1146 smoothNumbers23 :=
  sorry

end
