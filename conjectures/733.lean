import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical

noncomputable section

/-!
# Erdős Problem #733

Call a sequence 1 < X₁ ≤ ⋯ ≤ X_m ≤ n line-compatible if there is a set of n
points in ℝ² such that there are m lines ℓ₁, …, ℓ_m containing at least two
points, and the number of points on ℓᵢ is exactly Xᵢ.

Prove that there are at most exp(O(√n)) many line-compatible sequences.

This is essentially the same as problem [607], but with multiplicities.
Proved by Szemerédi and Trotter [SzTr83].
See also [732].
-/

/-- Three points in ℝ² are collinear: the cross product of the displacement
    vectors (q - p) and (r - p) vanishes. -/
def Collinear733 (p q r : ℝ × ℝ) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/-- A line determined by a point set P: the set of all points in P collinear
    with a given pair of distinct points. -/
def IsLine733 (P : Finset (ℝ × ℝ)) (L : Finset (ℝ × ℝ)) : Prop :=
  L ⊆ P ∧ 2 ≤ L.card ∧
  ∃ p q : ℝ × ℝ, p ∈ P ∧ q ∈ P ∧ p ≠ q ∧
    L = P.filter (fun r => Collinear733 p q r)

/-- A multiset of natural numbers is line-compatible for n if there exists a
    point set P of size n in ℝ² whose collection of determined lines yields
    that multiset of sizes. -/
def IsLineCompatible733 (n : ℕ) (M : Multiset ℕ) : Prop :=
  ∃ P : Finset (ℝ × ℝ), P.card = n ∧
    ∃ lines : Finset (Finset (ℝ × ℝ)),
      (∀ L ∈ lines, IsLine733 P L) ∧
      (∀ L, IsLine733 P L → L ∈ lines) ∧
      lines.val.map Finset.card = M

/-- The set of achievable line-compatible multisets for n-point configurations
    in ℝ². -/
def achievableLineMultisets733 (n : ℕ) : Set (Multiset ℕ) :=
  {M | IsLineCompatible733 n M}

/--
**Erdős Problem #733** [Er81]:

There exists a constant C > 0 such that for all sufficiently large n, the number
of line-compatible sequences (multisets of line sizes from n-point configurations
in ℝ²) is at most exp(C · √n).

Proved by Szemerédi and Trotter [SzTr83].
-/
theorem erdos_problem_733 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (achievableLineMultisets733 n).Finite ∧
      ((achievableLineMultisets733 n).ncard : ℝ) ≤
        Real.exp (C * Real.sqrt (n : ℝ)) :=
  sorry

end
