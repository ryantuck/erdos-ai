import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Finset

noncomputable section

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-!
# Erdős Problem #155

Let $F(N)$ be the size of the largest Sidon subset of $\{1,\ldots,N\}$.
Is it true that for every $k\geq 1$ we have $F(N+k)\leq F(N)+1$
for all sufficiently large $N$?

A question of Erdős [Er92c][ESS94][Er94b]. This may even hold with
$k \approx \epsilon N^{1/2}$.
-/

/--
Erdős Problem #155:

For every k ≥ 1, for all sufficiently large N, every Sidon subset of
{0, ..., N+k-1} has size at most one more than the largest Sidon subset
of {0, ..., N-1}.

Equivalently: F(N+k) ≤ F(N) + 1, where F(N) = max {|A| : A ⊆ {0,...,N-1}, A Sidon}.
-/
theorem erdos_problem_155 :
    ∀ k : ℕ, 1 ≤ k →
      ∀ᶠ N : ℕ in atTop,
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + k) → IsSidonSet A →
          ∃ B : Finset ℕ, B ⊆ Finset.range N ∧ IsSidonSet B ∧ A.card ≤ B.card + 1 :=
  sorry

end
