import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Finset

/--
The least prime congruent to `a` modulo `d`, if one exists.
By Dirichlet's theorem, when gcd(a,d) = 1, there are infinitely many
such primes, so this is well-defined.
-/
noncomputable def leastPrimeInResidue (a d : ℕ) : ℕ :=
  Nat.find (show ∃ p, p.Prime ∧ p ≡ a [MOD d] ∧ 0 < p from sorry)

/--
Erdős Problem #971 [Er65b]:

Let p(a,d) be the least prime congruent to a (mod d). Does there exist a
constant c > 0 such that, for all sufficiently large d,
  p(a,d) > (1 + c) · φ(d) · log d
for at least C · φ(d) many values of a coprime to d (for some constant C > 0)?

Erdős could prove this for an infinite sequence of d. He also showed that for
any ε > 0, p(a,d) < ε · φ(d) · log d for ≫_ε φ(d) many values of a.
-/
theorem erdos_problem_971 :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ D : ℕ,
    ∀ d : ℕ, D ≤ d →
      C * (Nat.totient d : ℝ) ≤
        ((Finset.range d).filter fun a =>
          Nat.Coprime a d ∧
          (leastPrimeInResidue a d : ℝ) > (1 + c) * (Nat.totient d : ℝ) * Real.log d).card :=
  sorry
