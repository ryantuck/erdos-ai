import Mathlib.Data.Finset.Card
import Mathlib.Algebra.IsPrimePow

/--
A **finite projective plane of order n** is a collection of subsets (called lines)
of {1, …, n² + n + 1} where each line has size n + 1 and every pair of distinct
points is contained in exactly one line.
-/
def IsFiniteProjectivePlane (n : ℕ) (lines : Finset (Finset (Fin (n ^ 2 + n + 1)))) : Prop :=
  (∀ L ∈ lines, L.card = n + 1) ∧
  (∀ (p q : Fin (n ^ 2 + n + 1)), p ≠ q →
    ∃! L, L ∈ lines ∧ p ∈ L ∧ q ∈ L)

/--
Erdős Problem #723 [Er81]:

If there is a finite projective plane of order n then must n be a prime power?

A finite projective plane of order n is a collection of subsets of {1,…,n²+n+1}
of size n+1 such that every pair of elements is contained in exactly one set.
These always exist if n is a prime power.
-/
theorem erdos_problem_723
    (n : ℕ)
    (hn : 2 ≤ n)
    (lines : Finset (Finset (Fin (n ^ 2 + n + 1))))
    (hplane : IsFiniteProjectivePlane n lines) :
    IsPrimePow (n : ℕ) :=
  sorry
