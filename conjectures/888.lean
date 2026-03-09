import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic

/--
A set A ⊆ {1,…,n} has the **Erdős–Sárközy–Sós square property** if whenever
a ≤ b ≤ c ≤ d are elements of A with a * b * c * d a perfect square,
then a * d = b * c.
-/
def SquareProductProperty (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≤ b → b ≤ c → c ≤ d →
    IsSquare (a * b * c * d) →
    a * d = b * c

/--
Erdős Problem #888 [Er98,p.178]:

What is the size of the largest A ⊆ {1,…,n} such that if a ≤ b ≤ c ≤ d ∈ A
are such that abcd is a square then ad = bc?

A question of Erdős, Sárközy, and Sós. Sárközy proved |A| = o(n). The primes
show |A| ≫ n/log n is possible. The set of semiprimes gives
(1+o(1))(log log n / log n) · n ≤ |A|.

We state that |A| = o(n), i.e., for every ε > 0 and all sufficiently large n,
any such A has |A| ≤ ε * n.
-/
theorem erdos_problem_888 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ A : Finset ℕ,
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) →
          SquareProductProperty A →
          (A.card : ℝ) ≤ ε * (n : ℝ) :=
  sorry
