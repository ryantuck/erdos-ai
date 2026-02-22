import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #772

Let k ≥ 1 and H_k(n) be the maximal r such that if A ⊂ ℕ has |A| = n and
‖1_A ∗ 1_A‖_∞ ≤ k (the additive representation function is bounded by k)
then A contains a Sidon set of size at least r.

Is it true that H_k(n)/n^{1/2} → ∞? Or even H_k(n) > n^{1/2+c} for some
constant c > 0?

PROVED: The answer is yes, and in fact H_k(n) ≫_k n^{2/3}, proved by
Alon and Erdős [AlEr85].

https://www.erdosproblems.com/772

Tags: number theory, sidon sets, additive combinatorics
-/

/-- A finite set of natural numbers is a Sidon set (B₂ set) if all pairwise
    sums are distinct: for a, b, c, d ∈ S with a + b = c + d, we have
    {a, b} = {c, d} as multisets. -/
def IsSidonSet772 (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The additive representation count: the number of ordered pairs (a, b) ∈ A × A
    with a + b = m. The condition ‖1_A ∗ 1_A‖_∞ ≤ k is equivalent to
    addRepCount A m ≤ k for all m. -/
def addRepCount772 (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => a ≤ m ∧ (m - a) ∈ A)).card

/--
Erdős Problem #772 (PROVED, Alon–Erdős [AlEr85]):

For every k ≥ 1, H_k(n) ≫_k n^{2/3}. That is, for each k there exist C > 0
and N₀ such that for all n ≥ N₀, every set A ⊆ ℕ with |A| = n and additive
representation function bounded by k (i.e., ‖1_A ∗ 1_A‖_∞ ≤ k) contains a
Sidon subset of size at least C · n^{2/3}.
-/
theorem erdos_problem_772 (k : ℕ) (hk : k ≥ 1) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ A : Finset ℕ, A.card = n →
        (∀ m : ℕ, addRepCount772 A m ≤ k) →
        ∃ S : Finset ℕ, S ⊆ A ∧ IsSidonSet772 S ∧
          (S.card : ℝ) ≥ C * (n : ℝ) ^ ((2 : ℝ) / 3) :=
  sorry

end
