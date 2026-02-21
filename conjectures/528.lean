import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card

open Finset BigOperators Filter

/-- Two points in ℤ^k are adjacent in the integer lattice if their ℓ¹ distance
    is 1 (i.e., they differ by ±1 in exactly one coordinate). -/
def LatticeAdj {k : ℕ} (x y : Fin k → ℤ) : Prop :=
  (∑ i : Fin k, |x i - y i|) = 1

/-- The number of self-avoiding walks of n steps in ℤ^k starting at the origin.
    A self-avoiding walk is a path in the integer lattice ℤ^k that starts at the
    origin, takes n steps along lattice edges, and never revisits a vertex. -/
noncomputable def selfAvoidingWalkCount (n k : ℕ) : ℕ :=
  Set.ncard {w : Fin (n + 1) → (Fin k → ℤ) |
    w 0 = 0 ∧
    (∀ i : Fin n, LatticeAdj (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)) ∧
    Function.Injective w}

/--
Erdős Problem #528 (Connective Constant for Self-Avoiding Walks):

Let f(n,k) count the number of self-avoiding walks of n steps beginning at the
origin in ℤ^k (those walks which do not intersect themselves). The connective
constant C_k is defined as C_k = lim_{n→∞} f(n,k)^{1/n}.

Hammersley and Morton [HM54] showed this limit exists. It is trivially true that
k ≤ C_k ≤ 2k-1. Kesten [Ke63] proved C_k = 2k-1-1/(2k)+O(1/k²).

The problem asks to determine C_k exactly. We formalize the existence of the
connective constant together with the known bounds k ≤ C_k ≤ 2k-1.
-/
theorem erdos_problem_528 :
    ∀ k : ℕ, 0 < k →
    ∃ C : ℝ,
      (k : ℝ) ≤ C ∧ C ≤ 2 * (k : ℝ) - 1 ∧
      Filter.Tendsto
        (fun n : ℕ => ((selfAvoidingWalkCount n k : ℝ)) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds C) :=
  sorry
