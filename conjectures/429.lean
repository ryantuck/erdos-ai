import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #429 (Disproved):
Is it true that, if A ⊆ ℕ is sparse enough and does not cover all residue
classes modulo p for any prime p, then there exists some n such that n + a
is prime for all a ∈ A?

A set A ⊆ ℕ is called "admissible" if for every prime p, there exists a
residue class modulo p not represented in A. This is a necessary condition
for the translate A + n to consist entirely of primes.

Weisenberg [We24] has shown the answer is no: A can be arbitrarily sparse
and missing at least one residue class modulo every prime p, and yet A + n
is not contained in the primes for any n ∈ ℤ.

We formalize the conjecture for infinite admissible sets A ⊆ ℕ.
-/
theorem erdos_problem_429 :
  ∀ (A : Set ℕ),
    Set.Infinite A →
    (∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ r) →
    ∃ n : ℕ, ∀ a ∈ A, (n + a).Prime :=
  sorry
