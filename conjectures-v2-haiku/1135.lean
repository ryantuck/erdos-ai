import Mathlib.Data.Nat.Basic

/--
The Collatz function: f(n) = n/2 if n is even, f(n) = (3n+1)/2 if n is odd.
-/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/--
The k-th iterate of the Collatz function.
-/
def collatzIter (k : ℕ) (n : ℕ) : ℕ :=
  match k with
  | 0 => n
  | k + 1 => collatzStep (collatzIter k n)

/--
Erdős Problem #1135 [La85, Er97e, La16]:

Define f : ℕ → ℕ by f(n) = n/2 if n is even and f(n) = (3n+1)/2 if n is odd.

Given any integer m ≥ 1, does there exist k ≥ 1 such that f^(k)(m) = 1?

This is the infamous Collatz conjecture. It is not a problem due to Erdős; it was
first devised by Collatz before 1952. Erdős referred to this problem on several
occasions as 'hopeless', saying "Mathematics may not be ready for such problems".

Bibliography:
[La85] Lagarias, J. C. "The 3x+1 Problem and Its Generalizations." The American
       Mathematical Monthly, vol. 92, no. 1, 1985, pp. 3–23.
[Er97e] Erdős, P. Personal remarks on the Collatz conjecture, 1997.
[La16] Lagarias, J. C. (Ed.). The Ultimate Challenge: The 3x+1 Problem. American
        Mathematical Society, 2016.
-/
theorem erdos_problem_1135 :
    ∀ m : ℕ, 1 ≤ m → answer(sorry) ↔ ∃ k : ℕ, 1 ≤ k ∧ collatzIter k m = 1 := by
  sorry
