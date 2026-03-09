import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

open Classical

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The k-fold sumset of a set B ⊆ ℕ: the set of all sums of at most k elements of B.
-/
def kFoldSumset (B : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => {n | ∃ m ∈ kFoldSumset B k, ∃ b ∈ B, n = m + b} ∪ kFoldSumset B k

/--
A set B ⊆ ℕ is an additive basis if there exists k such that every natural number
can be written as the sum of at most k elements of B.
-/
def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, n ∈ kFoldSumset B k

/--
The translate of a set A by b: A + b = {a + b | a ∈ A}.
-/
def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, n = a + b}

/--
Erdős Problem #38 [Er56, p.136]:

Does there exist B ⊂ ℕ which is not an additive basis, but is such that for
every set A ⊆ ℕ of Schnirelmann density α and every N there exists b ∈ B such that
  |(A ∪ (A + b)) ∩ {1,...,N}| ≥ (α + f(α)) · N
where f(α) > 0 for 0 < α < 1?

This is a stronger property than B being an essential component (see problem #37).
-/
theorem erdos_problem_38 :
    ∃ (B : Set ℕ), ¬IsAdditiveBasis B ∧
      ∃ (f : ℝ → ℝ), (∀ α : ℝ, 0 < α → α < 1 → 0 < f α) ∧
        ∀ (A : Set ℕ), ∀ (N : ℕ+),
          let α := schnirelmannDensity A
          ∃ b ∈ B,
            (((Finset.Icc 1 (N : ℕ)).filter (· ∈ A ∪ translateSet A b)).card : ℝ) ≥
              (α + f α) * (N : ℝ) :=
  sorry
