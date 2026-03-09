import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.GCD.Basic

/--
Erdős Problem #402 [Er73, ErGr80]:

Prove that, for any finite set A ⊂ ℕ, there exist a, b ∈ A such that
gcd(a, b) ≤ a / |A|.

A conjecture of Graham, proved for all sufficiently large sets independently
by Szegedy and Zaharescu, and for all sets by Balasubramanian and
Soundararajan.
-/
theorem erdos_problem_402
    (A : Finset ℕ) (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    ∃ a ∈ A, ∃ b ∈ A, Nat.gcd a b ≤ a / A.card :=
  sorry
