import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

/--
A generalized Fibonacci (Lucas) sequence over ℕ:
  a(n+2) = a(n+1) + a(n) for all n.
-/
def IsLucasSeq (a : ℕ → ℕ) : Prop :=
  ∀ n, a (n + 2) = a (n + 1) + a n

/--
Erdős Problem #276 [ErGr80, p.27]:

Is there an infinite Lucas sequence a₀, a₁, … where a_{n+2} = a_{n+1} + aₙ
such that all terms are composite, and yet no integer ≥ 2 divides every term
of the sequence?

Graham [Gr64] showed that composite Lucas sequences exist using covering
systems. This problem asks whether one can exist without an underlying system
of covering congruences being responsible — equivalently, whether the gcd of
all terms can equal 1.
-/
theorem erdos_problem_276 :
    ∃ a : ℕ → ℕ,
      IsLucasSeq a ∧
      (∀ k, ¬ Nat.Prime (a k) ∧ a k > 1) ∧
      (¬ ∃ d : ℕ, d ≥ 2 ∧ ∀ k, d ∣ a k) :=
  sorry
