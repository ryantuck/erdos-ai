import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum

open Set Cardinal Topology

noncomputable section

/-!
# Erdős Problem #910

Does every connected set in ℝⁿ contain a connected subset which is not a point
and not homeomorphic to the original set?

If n ≥ 2, does every connected set in ℝⁿ contain more than 2^ℵ₀ many connected
subsets?

Asked by Erdős in the 1940s, who thought the answer to both questions is yes.
The answer to both is in fact no, as shown by Rudin [Ru58] (conditional on the
continuum hypothesis).

Tags: topology
-/

/--
Erdős Problem #910, Part 1 (disproved by Rudin [Ru58]):

Every connected set in ℝⁿ contains a connected subset which is not a single
point and not homeomorphic to the original set.
-/
theorem erdos_problem_910a (n : ℕ) (hn : n ≥ 1) :
    ∀ (S : Set (EuclideanSpace ℝ (Fin n))),
    IsConnected S →
    ∃ (T : Set (EuclideanSpace ℝ (Fin n))),
      T ⊆ S ∧ IsConnected T ∧ T.Nontrivial ∧
      IsEmpty (Homeomorph T S) :=
  sorry

/--
Erdős Problem #910, Part 2 (disproved by Rudin [Ru58]):

If n ≥ 2, every connected set in ℝⁿ has more than 2^ℵ₀ many connected subsets.
-/
theorem erdos_problem_910b (n : ℕ) (hn : n ≥ 2) :
    ∀ (S : Set (EuclideanSpace ℝ (Fin n))),
    IsConnected S →
    Cardinal.continuum < #{T : Set (EuclideanSpace ℝ (Fin n)) // T ⊆ S ∧ IsConnected T} :=
  sorry

end
