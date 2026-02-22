import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic

open Set

/-!
# Erdős Problem #1003

Are there infinitely many solutions to φ(n) = φ(n+1), where φ is the Euler
totient function?

Erdős [Er85e] says that, presumably, for every k ≥ 1 the equation
  φ(n) = φ(n+1) = ⋯ = φ(n+k)
has infinitely many solutions.
-/

/--
Erdős Problem #1003 [Er85e]:

Are there infinitely many n such that φ(n) = φ(n+1)?
-/
theorem erdos_problem_1003 :
    Set.Infinite {n : ℕ | Nat.totient n = Nat.totient (n + 1)} :=
  sorry

/--
Erdős Problem #1003 (stronger form) [Er85e]:

For every k ≥ 1, there are infinitely many n such that
  φ(n) = φ(n+1) = ⋯ = φ(n+k).
-/
theorem erdos_problem_1003_consecutive (k : ℕ) (hk : k ≥ 1) :
    Set.Infinite {n : ℕ | ∀ i : ℕ, 1 ≤ i → i ≤ k →
      Nat.totient n = Nat.totient (n + i)} :=
  sorry
