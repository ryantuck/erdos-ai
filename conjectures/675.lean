import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Classical

noncomputable section

/-!
# Erdős Problem #675

We say that A ⊂ ℕ has the translation property if, for every n, there exists
some integer t_n ≥ 1 such that, for all 1 ≤ a ≤ n,
  a ∈ A if and only if a + t_n ∈ A.

Three questions:
1. Does the set of sums of two squares have the translation property?
2. If we partition all primes into P ⊔ Q, such that each set contains ≫ x/log x
   many primes ≤ x for all large x, then can the set of integers only divisible
   by primes from P have the translation property?
3. If A is the set of squarefree numbers then how fast does the minimal such t_n
   grow? Is it true that t_n > exp(n^c) for some constant c > 0?

Elementary sieve theory implies the set of squarefree numbers has the
translation property.
-/

/-- A set A ⊆ ℕ has the translation property if for every n, there exists
    t ≥ 1 such that for all 1 ≤ a ≤ n, a ∈ A ↔ a + t ∈ A. -/
def HasTranslationProperty (A : Set ℕ) : Prop :=
  ∀ n : ℕ, ∃ t : ℕ, t ≥ 1 ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)

/-- A natural number is a sum of two squares. -/
def IsSumOfTwoSquares675 (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- The set of natural numbers that are sums of two squares. -/
def sumOfTwoSquaresSet : Set ℕ := {n | IsSumOfTwoSquares675 n}

/-- The set of squarefree natural numbers. -/
def squarefreeSet675 : Set ℕ := {n | Squarefree n}

/-- The minimal translation witness for a set A at level n:
    the smallest t ≥ 1 such that for all 1 ≤ a ≤ n, a ∈ A ↔ a + t ∈ A. -/
noncomputable def minimalTranslation675 (A : Set ℕ) (n : ℕ) : ℕ :=
  sInf {t : ℕ | t ≥ 1 ∧ ∀ a : ℕ, 1 ≤ a → a ≤ n → (a ∈ A ↔ a + t ∈ A)}

/-- Given a set of primes P, the set of natural numbers ≥ 1 all of whose
    prime factors lie in P. -/
def smoothNumbers675 (P : Set ℕ) : Set ℕ :=
  {n | n ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ∈ P}

/--
Erdős Problem #675, Part 1 [Er79]:

Does the set of sums of two squares have the translation property?
-/
theorem erdos_problem_675_part1 :
    HasTranslationProperty sumOfTwoSquaresSet :=
  sorry

/--
Erdős Problem #675, Part 2 [Er79]:

If we partition all primes into P ⊔ Q, such that each set contains ≫ x/log x
many primes ≤ x for all large x, then can the set of integers only divisible
by primes from P have the translation property?

Formalized as: for any such partition, the P-smooth numbers do NOT have
the translation property.
-/
theorem erdos_problem_675_part2 :
    ∀ (P : Set ℕ),
    (∃ c₁ : ℝ, c₁ > 0 ∧ ∃ N₁ : ℕ, ∀ x : ℕ, x ≥ N₁ →
      c₁ * (x : ℝ) / Real.log (x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun q => Nat.Prime q ∧ q ∈ P)).card : ℝ)) →
    (∃ c₂ : ℝ, c₂ > 0 ∧ ∃ N₂ : ℕ, ∀ x : ℕ, x ≥ N₂ →
      c₂ * (x : ℝ) / Real.log (x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun q => Nat.Prime q ∧ q ∉ P)).card : ℝ)) →
    ¬ HasTranslationProperty (smoothNumbers675 P) :=
  sorry

/--
Erdős Problem #675, Part 3 [Er79]:

If A is the set of squarefree numbers, then the minimal translation t_n
grows faster than exp(n^c) for some constant c > 0. That is, there exists
c > 0 and N₀ such that for all n ≥ N₀, t_n > exp(n^c).
-/
theorem erdos_problem_675_part3 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (minimalTranslation675 squarefreeSet675 n : ℝ) > Real.exp ((n : ℝ) ^ c) :=
  sorry

end
