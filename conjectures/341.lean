import Mathlib.Order.Monotone.Basic

/--
A strictly increasing sequence `a : ℕ → ℕ` is a Dickson extension with `k` initial
terms if, for every `n ≥ k`, `a n` is the least integer greater than `a (n - 1)` that
cannot be written as `a i + a j` for any `i, j < n`.
-/
def IsDicksonExtension (a : ℕ → ℕ) (k : ℕ) : Prop :=
  StrictMono a ∧
  ∀ n, k ≤ n →
    (∀ i j, i < n → j < n → a n ≠ a i + a j) ∧
    (∀ m, a (n - 1) < m → m < a n → ∃ i j, i < n ∧ j < n ∧ m = a i + a j)

/--
Erdős Problem #341 (Dickson's conjecture) [ErGr80, p.53]:
Let A = {a₁ < ⋯ < aₖ} be a finite set of positive integers. Extend it to an infinite
sequence by defining aₙ₊₁ (for n ≥ k) to be the least integer exceeding aₙ that is
not of the form aᵢ + aⱼ with i, j ≤ n. Is it true that the sequence of consecutive
differences aₘ₊₁ - aₘ is eventually periodic?
-/
theorem erdos_problem_341 :
    ∀ (a : ℕ → ℕ) (k : ℕ), 1 ≤ k →
      IsDicksonExtension a k →
      ∃ N p : ℕ, 1 ≤ p ∧
        ∀ m, N ≤ m → a (m + p + 1) - a (m + p) = a (m + 1) - a m :=
  sorry
