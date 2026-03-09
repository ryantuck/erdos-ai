import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic

/--
A "disjoint covering system from divisors of n" is a choice of residues
a_d for each divisor d > 1 of n such that:
1. Every integer is covered by some residue class a_d mod d (covering).
2. If some integer x lies in both a_d mod d and a_{d'} mod d', then gcd(d,d')=1.
-/
def DisjointDivisorCovering (n : ℕ) (a : ℕ → ℤ) : Prop :=
  -- Covering: every integer is covered by some divisor class
  (∀ x : ℤ, ∃ d ∈ n.divisors, d > 1 ∧ x ≡ a d [ZMOD (d : ℤ)]) ∧
  -- Disjointness: overlapping classes must have coprime moduli
  (∀ d ∈ n.divisors, d > 1 →
    ∀ d' ∈ n.divisors, d' > 1 → d ≠ d' →
      (∃ x : ℤ, x ≡ a d [ZMOD (d : ℤ)] ∧ x ≡ a d' [ZMOD (d' : ℤ)]) →
        Nat.Coprime d d')

/--
Erdős Problem #204 [ErGr80, p.27]:

Are there n such that there is a covering system with moduli the divisors
of n which is 'as disjoint as possible'? That is, for all d ∣ n with d > 1
there is an associated a_d such that every integer is congruent to some
a_d (mod d), and if some integer x satisfies x ≡ a_d (mod d) and
x ≡ a_{d'} (mod d'), then gcd(d, d') = 1.

Erdős and Graham believed no such n exist. The density of such n is zero.
Adenwalla [Ad25] proved that no such n exist (DISPROVED).
-/
theorem erdos_problem_204 :
    ∀ n : ℕ, n > 0 →
      ¬∃ a : ℕ → ℤ, DisjointDivisorCovering n a :=
  sorry
