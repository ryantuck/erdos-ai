import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section

open Classical Finset BigOperators

/-!
# Erdős Problem #991

Suppose A = {w₁, …, wₙ} ⊂ S² maximises ∏_{i<j} |wᵢ - wⱼ| over all
possible sets of size n (such sets are called Fekete points).

Is it true that
  max_C | |A ∩ C| - α_C · n | = o(n),
where the maximum is taken over all spherical caps C and α_C is the area
of C (normalised so that the entire sphere has area 1)?

This was proved. Brauchart [Br08] showed O(n^{3/4}) and Marzo–Mas [MaMa21]
improved this to O(n^{2/3}).
-/

/-- The product of pairwise distances of a finite set of points. -/
noncomputable def pairwiseDistProd (P : Finset (EuclideanSpace ℝ (Fin 3))) : ℝ :=
  ∏ p ∈ P.offDiag, ‖p.1 - p.2‖

/-- A finite set of points on S² maximises the pairwise distance product
    among all sets of the same cardinality on S². -/
def IsMaxPairwiseDist (P : Finset (EuclideanSpace ℝ (Fin 3))) : Prop :=
  (∀ p ∈ P, ‖p‖ = 1) ∧
  ∀ (Q : Finset (EuclideanSpace ℝ (Fin 3))),
    (∀ q ∈ Q, ‖q‖ = 1) → Q.card = P.card →
    pairwiseDistProd Q ≤ pairwiseDistProd P

/--
Erdős Problem #991 [Er64b]:

If A = {w₁, …, wₙ} ⊂ S² are Fekete points (maximising the product of
pairwise distances), then the spherical cap discrepancy of A is o(n):
for every ε > 0, if n is large enough and P is any set of n Fekete points,
then for every spherical cap C(v,t) = {x ∈ S² : ⟨x,v⟩ ≥ t},
  ||P ∩ C(v,t)| − ((1−t)/2) · n| ≤ ε · n.

Here (1−t)/2 is the normalised surface area of the cap C(v,t) on S².
-/
theorem erdos_problem_991 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ (P : Finset (EuclideanSpace ℝ (Fin 3))),
      IsMaxPairwiseDist P →
      P.card ≥ N₀ →
      ∀ (v : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
        ‖v‖ = 1 → -1 ≤ t → t ≤ 1 →
        |((P.filter (fun x => @inner ℝ _ _ x v ≥ t)).card : ℝ) -
          (1 - t) / 2 * (P.card : ℝ)| ≤ ε * (P.card : ℝ) :=
  sorry

end
