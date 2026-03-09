import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

/--
A system of congruences is a finite collection of pairs (aᵢ, nᵢ) where each
pair represents the residue class aᵢ (mod nᵢ).
-/
structure CongruenceSystem where
  /-- The number of congruences in the system -/
  size : ℕ
  /-- The residues -/
  residue : Fin size → ℤ
  /-- The moduli (all positive) -/
  modulus : Fin size → ℕ
  /-- Each modulus is at least 1 -/
  modulus_pos : ∀ i, 0 < modulus i

/--
An integer m is covered by a system of congruences if there exists some
index i such that m ≡ aᵢ (mod nᵢ).
-/
def CongruenceSystem.covers (S : CongruenceSystem) (m : ℤ) : Prop :=
  ∃ i : Fin S.size, m % (S.modulus i : ℤ) = S.residue i % (S.modulus i : ℤ)

/--
A system of congruences covers a set of consecutive integers starting at k
of length L if every integer in {k, k+1, ..., k+L-1} is covered.
-/
def CongruenceSystem.coversConsecutive (S : CongruenceSystem) (k : ℤ) (L : ℕ) : Prop :=
  ∀ j : Fin L, S.covers (k + j)

/--
A system of congruences covers all integers.
-/
def CongruenceSystem.coversAll (S : CongruenceSystem) : Prop :=
  ∀ m : ℤ, S.covers m

/--
Erdős Problem #275 [Er65, Er65b, ErGr80]:

If a finite system of r congruences {aᵢ (mod nᵢ) : 1 ≤ i ≤ r} (the nᵢ are
not necessarily distinct) covers 2^r consecutive integers, then it covers all
integers.

This is best possible, as the system 2^{i-1} (mod 2^i) shows.
Proved independently by Selfridge and by Crittenden–Vanden Eynden [CrVE70].
-/
theorem erdos_problem_275 (S : CongruenceSystem) :
    ∀ k : ℤ, S.coversConsecutive k (2 ^ S.size) → S.coversAll :=
  sorry
