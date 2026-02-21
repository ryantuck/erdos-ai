import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs

open Classical

/-!
# Erdős Problem #278: Covering Congruences Density

Let A = {n₁, ..., nᵣ} be a finite set of positive integers. For any choice of
residues a₁, ..., aᵣ, consider the set of integers covered by the union of
congruence classes m ≡ aᵢ (mod nᵢ). The covering density is the natural density
of this set (which exists since the covered set is periodic with period lcm(A)).

Open question (Erdős–Graham [ErGr80,p.28]): What is the maximum covering density
achievable by a suitable choice of the aᵢ?

Settled (Simpson [Si86]): The minimum covering density is achieved when all aᵢ
are equal, and equals the inclusion-exclusion sum
  ∑ᵢ 1/nᵢ - ∑_{i<j} 1/lcm(nᵢ,nⱼ) + ∑_{i<j<k} 1/lcm(nᵢ,nⱼ,nₖ) - ⋯
-/

/-- The covering density of congruences m ≡ offsets(n) (mod n) for n ∈ moduli.
    Since the covered set is periodic with period L = lcm(moduli), the density equals
    |{m ∈ {0,...,L-1} : ∃ n ∈ moduli, n ∣ (m - offsets(n))}| / L. -/
noncomputable def coveringDensity (moduli : Finset ℕ) (offsets : ℕ → ℤ) : ℚ :=
  let L := moduli.lcm id
  let covered := (Finset.range L).filter fun (m : ℕ) =>
    ∃ n ∈ moduli, (n : ℤ) ∣ ((m : ℤ) - offsets n)
  (covered.card : ℚ) / (L : ℚ)

/-- The inclusion-exclusion density for a set of moduli: the alternating sum
    ∑_{∅ ≠ S ⊆ moduli} (-1)^(|S|+1) / lcm(S).
    This equals the covering density when all offsets are equal. -/
noncomputable def inclusionExclusionDensity (moduli : Finset ℕ) : ℚ :=
  ((moduli.powerset.filter fun S => S.Nonempty).sum fun S =>
    (-1 : ℚ) ^ (S.card + 1) / ((S.lcm id : ℕ) : ℚ))

/--
Erdős Problem #278 (Simpson's theorem [Si86]):

For a finite set of positive integer moduli, the minimum covering density over all
choices of offsets equals the inclusion-exclusion density. Specifically:
(1) For any choice of offsets, the covering density is at least the
    inclusion-exclusion density.
(2) This lower bound is achieved when all offsets are equal.

The maximum covering density (the original open question of Erdős–Graham [ErGr80,p.28])
remains unknown.
-/
theorem erdos_problem_278 (moduli : Finset ℕ) (h : ∀ n ∈ moduli, 0 < n) :
    (∀ offsets : ℕ → ℤ,
      inclusionExclusionDensity moduli ≤ coveringDensity moduli offsets) ∧
    (∀ a : ℤ,
      coveringDensity moduli (fun _ => a) = inclusionExclusionDensity moduli) :=
  sorry
