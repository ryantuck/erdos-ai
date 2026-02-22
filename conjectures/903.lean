import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card

noncomputable section

/-!
# Erdős Problem #903

Let n = p² + p + 1 for some prime power p, and let A₁, ..., Aₜ ⊆ {1, ..., n}
be a block design (so that every pair x, y ∈ {1, ..., n} is contained in
exactly one Aᵢ).

Is it true that if t > n then t ≥ n + p?

A conjecture of Erdős and Sós. The classic finite geometry construction shows
that t = n is possible. A theorem of Erdős and de Bruijn [dBEr48] states that
t ≥ n. This was proved by Erdős, Fowler, Sós, and Wilson [EFSW85], who further
show that unless the block design is obtained from a projective plane by
'breaking up' one of its lines then t ≥ n + cp where c ≈ 1.148.

Tags: combinatorics
-/

/-- A pairwise balanced design on Fin n: a family of blocks (subsets) such that
    every pair of distinct elements is contained in exactly one block. -/
def IsPairwiseBalancedDesign {n : ℕ} (blocks : Finset (Finset (Fin n))) : Prop :=
  ∀ x y : Fin n, x ≠ y →
    ∃! B : Finset (Fin n), B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/--
Erdős Problem #903 [Er82e]:

Let n = p² + p + 1 for a prime power p (i.e., p = q^k for some prime q and
k ≥ 1), and let blocks be a pairwise balanced design on {0, ..., n-1} (every
pair of distinct elements appears in exactly one block). If the number of
blocks t > n, then t ≥ n + p.

Proved by Erdős, Fowler, Sós, and Wilson [EFSW85].
-/
theorem erdos_problem_903 (p q k : ℕ) (hq : Nat.Prime q) (hk : k ≥ 1)
    (hp : p = q ^ k)
    (n : ℕ) (hn : n = p ^ 2 + p + 1)
    (blocks : Finset (Finset (Fin n)))
    (hdesign : IsPairwiseBalancedDesign blocks)
    (hgt : blocks.card > n) :
    blocks.card ≥ n + p :=
  sorry

end
