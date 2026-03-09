import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Finset Filter

noncomputable section

/--
The counting function for a set A ⊆ ℕ restricted to {1, …, N}:
  |A ∩ {1, …, N}|
-/
def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/--
The sumset counting function: the number of elements in (A + A) ∩ {1, …, N},
where A + A = {a + b | a, b ∈ A}.
-/
def sumsetCountingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard ({n ∈ Set.Icc 1 N | ∃ a ∈ A, ∃ b ∈ A, n = a + b})

/--
Erdős Problem #245 [Er61, ErGr80, Er82e]:

Let A ⊆ ℕ be an infinite set of positive integers with zero natural density,
i.e., |A ∩ {1,…,N}| = o(N). Is it true that
  limsup_{N → ∞} |(A + A) ∩ {1,…,N}| / |A ∩ {1,…,N}| ≥ 3?

Erdős writes it is 'easy to see' that this holds with 3 replaced by 2 (this
follows from a result of Mann), and that 3 would be best possible.
The answer is yes, proved by Freiman (1973).
-/
theorem erdos_problem_245
    (A : Set ℕ)
    (hA_pos : A ⊆ Set.Ici 1)
    (hA_inf : Set.Infinite A)
    (hA_density : Tendsto (fun N : ℕ => (countingFn A N : ℝ) / (N : ℝ)) atTop (nhds 0)) :
    ∀ c : ℝ, c < 3 →
      ∀ N₀ : ℕ, ∃ N ≥ N₀,
        (c : ℝ) * (countingFn A N : ℝ) ≤ (sumsetCountingFn A N : ℝ) :=
  sorry

end
