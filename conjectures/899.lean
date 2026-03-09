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
The difference set counting function: the number of elements in (A - A) ∩ {1, …, N},
where A - A = {a - b | a, b ∈ A, a > b}.
-/
def diffsetCountingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard ({n ∈ Set.Icc 1 N | ∃ a ∈ A, ∃ b ∈ A, n + b = a})

/--
Erdős Problem #899 [Er82e]:

Let A ⊆ ℕ be an infinite set of positive integers with zero natural density,
i.e., |A ∩ {1,…,N}| = o(N). Is it true that
  limsup_{N → ∞} |(A - A) ∩ {1,…,N}| / |A ∩ {1,…,N}| = ∞?

Here A - A denotes the set of positive differences {a - b : a, b ∈ A, a > b}.

The answer is yes, proved by Ruzsa [Ru78].
See also [245] for the sum set analogue.
-/
theorem erdos_problem_899
    (A : Set ℕ)
    (hA_pos : A ⊆ Set.Ici 1)
    (hA_inf : Set.Infinite A)
    (hA_density : Tendsto (fun N : ℕ => (countingFn A N : ℝ) / (N : ℝ)) atTop (nhds 0)) :
    ∀ c : ℝ,
      ∀ N₀ : ℕ, ∃ N ≥ N₀,
        (c : ℝ) * (countingFn A N : ℝ) ≤ (diffsetCountingFn A N : ℝ) :=
  sorry

end
