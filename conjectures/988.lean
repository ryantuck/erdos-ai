import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic

noncomputable section

open Classical

/-!
# Erdős Problem #988

If P ⊆ S² is a subset of the unit sphere then define the discrepancy
  D(P) = max_C | |C ∩ P| - α_C |P| |,
where the maximum is taken over all spherical caps C, and α_C is the
appropriately normalised measure of C.

Is it true that min_{|P|=n} D(P) → ∞ as n → ∞?

This was proved (in any number of dimensions) by Schmidt [Sc69b].
-/

/--
Erdős Problem #988 [Er64b]:

For every M > 0, there exists N₀ such that for every finite set P of points
on the unit sphere S² in ℝ³ with |P| ≥ N₀, there exists a spherical cap
C(v,t) = {x ∈ S² : ⟪x, v⟫ ≥ t} (with v a unit vector and t ∈ [-1,1])
such that the discrepancy ||C(v,t) ∩ P| - ((1-t)/2) · |P|| ≥ M.

Here (1-t)/2 is the normalised surface area measure of the cap C(v,t) on S².
-/
theorem erdos_problem_988 :
    ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ (P : Finset (EuclideanSpace ℝ (Fin 3))),
      (∀ p ∈ P, ‖p‖ = 1) →
      P.card ≥ N₀ →
      ∃ (v : EuclideanSpace ℝ (Fin 3)) (t : ℝ),
        ‖v‖ = 1 ∧ -1 ≤ t ∧ t ≤ 1 ∧
        |((P.filter (fun x => @inner ℝ _ _ x v ≥ t)).card : ℝ) -
          (1 - t) / 2 * (P.card : ℝ)| ≥ M :=
  sorry

end
