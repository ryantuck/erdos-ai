import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

open Finset

noncomputable section

/--
The set of **P-smooth positive integers**: natural numbers n ≥ 1 whose prime
factors all belong to P. This always includes 1 (vacuously, since 1 has no
prime factors).
-/
def smoothNumbers (P : Finset ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ P}

/--
Erdős Problem #269 [ErGr80, Er88c]:

Let P be a finite set of primes with |P| ≥ 2 and let {a₁ < a₂ < ⋯} be the
set of positive integers whose prime factors all lie in P (the P-smooth
numbers). Is the sum

  ∑ₙ 1 / lcm(a₁, …, aₙ)

irrational?

Here `a` enumerates the P-smooth numbers in strictly increasing order, and
`(Finset.range (n + 1)).lcm a` computes lcm(a(0), a(1), …, a(n)).

If P is infinite, Erdős noted (in [Er88c]) that the sum is always irrational
(and called this a "simple exercise"). He could also prove irrationality when
duplicate summands are removed.
-/
theorem erdos_problem_269
    (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p)
    (hcard : 2 ≤ P.card)
    (a : ℕ → ℕ)
    (ha_mem : ∀ n, a n ∈ smoothNumbers P)
    (ha_mono : StrictMono a)
    (ha_surj : ∀ m, m ∈ smoothNumbers P → ∃ n, a n = m) :
    Irrational (∑' n, (1 : ℝ) / ↑((Finset.range (n + 1)).lcm a)) :=
  sorry

end
