import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Erdős Problem #436

For prime p and k, m ≥ 2, let r(k,m,p) be the minimal r such that
r, r+1, …, r+m−1 are all k-th power residues modulo p.
Let Λ(k,m) = lim sup_{p→∞} r(k,m,p).

Hildebrand [Hi91] proved that Λ(k,2) is finite for all k ≥ 2.
Graham [Gr64g] proved that Λ(k,ℓ) = ∞ for all k ≥ 2 and ℓ ≥ 4.
Lehmer and Lehmer [LeLe62] proved that Λ(k,3) = ∞ for all even k.

The remaining open question is whether Λ(k,3) is finite for all odd k ≥ 5.
-/

/-- A natural number `a` is a k-th power residue modulo `p` if there exists
    `x` such that `x ^ k = a` in `ZMod p`. -/
def IsKthPowerResidueMod (k : ℕ) (a : ℕ) (p : ℕ) : Prop :=
  ∃ x : ZMod p, x ^ k = (a : ZMod p)

/-- `LambdaFinite k m` asserts that Λ(k,m) is finite: there exists a bound `R`
    such that for all sufficiently large primes `p`, there exist `m` consecutive
    k-th power residues modulo `p` starting at some `r` with `1 ≤ r ≤ R`. -/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ R : ℕ, ∃ N : ℕ, ∀ p : ℕ, p.Prime → p > N →
    ∃ r : ℕ, r ≥ 1 ∧ r ≤ R ∧ ∀ j : ℕ, j < m → IsKthPowerResidueMod k (r + j) p

/-- Erdős Problem #436, Hildebrand's theorem (PROVED):
    Λ(k,2) is finite for all k ≥ 2. For any k ≥ 2, if p is sufficiently large
    then there exists a pair of consecutive k-th power residues modulo p
    in [1, O_k(1)]. -/
theorem erdos_problem_436_hildebrand (k : ℕ) (hk : 2 ≤ k) :
    LambdaFinite k 2 :=
  sorry

/-- Erdős Problem #436, open conjecture:
    Λ(k,3) is finite for all odd k ≥ 5. For any odd k ≥ 5, if p is sufficiently
    large then there exist three consecutive k-th power residues modulo p
    in [1, O_k(1)]. -/
theorem erdos_problem_436_conjecture (k : ℕ) (hk : 5 ≤ k) (hodd : k % 2 = 1) :
    LambdaFinite k 3 :=
  sorry
