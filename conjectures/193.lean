import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Erdős Problem #193

Let S ⊆ ℤ³ be a finite set and let A = {a₁, a₂, …} ⊂ ℤ³ be an infinite
S-walk, so that aᵢ₊₁ - aᵢ ∈ S for all i. Must A contain three collinear points?

Originally conjectured by Gerver and Ramsey [GeRa79], who showed that the
answer is yes for ℤ², and for ℤ³ that the largest number of collinear points
can be bounded.
-/

/-- Three points in ℤ³ are collinear if the difference vectors from the first
    to the other two are linearly dependent over ℤ (equivalently, over ℚ). -/
def Collinear3 (p q r : Fin 3 → ℤ) : Prop :=
  ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ k : Fin 3, a * (q k - p k) = b * (r k - p k)

/--
Erdős Problem #193 [ErGr79, ErGr80]:
Let S ⊆ ℤ³ be a finite set and let a : ℕ → ℤ³ be an injective S-walk
(i.e. a(i+1) - a(i) ∈ S for all i, visiting infinitely many distinct points).
Then the range of a must contain three collinear points.
-/
theorem erdos_problem_193 :
    ∀ (S : Finset (Fin 3 → ℤ)) (a : ℕ → (Fin 3 → ℤ)),
      Function.Injective a →
      (∀ i, a (i + 1) - a i ∈ S) →
      ∃ i j k : ℕ, i < j ∧ j < k ∧ Collinear3 (a i) (a j) (a k) := by
  sorry
