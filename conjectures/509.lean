import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Complex Polynomial Metric Set BigOperators Finset

noncomputable section

/-!
# Erdős Problem #509

Let f(z) ∈ ℂ[z] be a monic non-constant polynomial. Can the set
  { z ∈ ℂ : |f(z)| ≤ 1 }
be covered by a set of circles the sum of whose radii is ≤ 2?

Cartan proved this is true with 2 replaced by 2e, which was improved
to 2.59 by Pommerenke [Po61]. Pommerenke [Po59] proved that 2 is
achievable if the set is connected (see problem #1046).
-/

/--
Erdős Problem #509 [Er61,p.246][Ha74]:

For any monic non-constant polynomial f ∈ ℂ[z], the set
  { z ∈ ℂ : ‖f(z)‖ ≤ 1 }
can be covered by finitely many closed discs whose radii sum to at most 2.
-/
theorem erdos_problem_509 (f : Polynomial ℂ) (hf : f.Monic)
    (hdeg : 0 < f.natDegree) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ),
      (∀ i, 0 ≤ r i) ∧
      {z : ℂ | ‖Polynomial.eval z f‖ ≤ 1} ⊆ ⋃ i, closedBall (c i) (r i) ∧
      ∑ i, r i ≤ 2 :=
  sorry

end
