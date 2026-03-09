import Mathlib.NumberTheory.Divisors

open Finset

/--
The number of divisors function τ(n) = |{d : d ∣ n}|.
-/
noncomputable def numDivisors (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/--
The function h(n) = n + τ(n).
-/
noncomputable def h (n : ℕ) : ℕ :=
  n + numDivisors n

/--
The k-th iterate of h:
h₀(n) = n, hₖ(n) = h(hₖ₋₁(n)).
-/
noncomputable def iterH : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => h (iterH k n)

/--
Erdős Problem #414 [ErGr80, p.82]:

Let h₁(n) = h(n) = n + τ(n), where τ(n) counts the number of divisors of n,
and hₖ(n) = h(hₖ₋₁(n)). Is it true that for any m, n, there exist i and j
such that hᵢ(m) = hⱼ(n)?

That is, there is (eventually) only one possible sequence that the iterations
of n ↦ h(n) can settle on. Asked by Spiro.
-/
theorem erdos_problem_414 :
    ∀ m n : ℕ, ∃ i j : ℕ, iterH i m = iterH j n :=
  sorry
