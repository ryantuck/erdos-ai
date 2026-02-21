import Mathlib.Algebra.Group.Even

/-!
# Erdős Problem #363 (DISPROVED)

Is it true that there are only finitely many collections of disjoint intervals
I₁, ..., Iₙ of consecutive integers with |Iᵢ| ≥ 4 for all i, such that
∏ᵢ ∏_{m ∈ Iᵢ} m is a perfect square?

This was disproved:
- Ulas [Ul05] proved infinitely many solutions exist when n = 4 or n ≥ 6, |Iᵢ| = 4.
- Bauer and Bennett [BaBe07] proved the same for n = 3 and n = 5, |Iᵢ| = 4.
- Bennett and Van Luijk [BeVL12] found infinitely many solutions for n ≥ 5, |Iᵢ| = 5.

We formalize the negation (the true result): there are infinitely many collections
of 3 pairwise disjoint intervals, each of 4 consecutive integers, whose total
product is a perfect square. "Infinitely many" is expressed by saying that for any
bound N, there exists such a collection with all starting points above N.
-/

/-- The product of 4 consecutive natural numbers starting at `a`. -/
def prod4 (a : ℕ) : ℕ := a * (a + 1) * (a + 2) * (a + 3)

/--
Erdős Problem #363 (Disproved by Bauer–Bennett [BaBe07]):

For any N, there exist starting points a, b, c > N with a+4 ≤ b and b+4 ≤ c
(so the three intervals {a,...,a+3}, {b,...,b+3}, {c,...,c+3} are pairwise disjoint)
such that the product of all 12 elements is a perfect square.
-/
theorem erdos_problem_363 :
    ∀ N : ℕ, ∃ a b c : ℕ,
      N < a ∧ a + 4 ≤ b ∧ b + 4 ≤ c ∧
      IsSquare (prod4 a * prod4 b * prod4 c) :=
  sorry
