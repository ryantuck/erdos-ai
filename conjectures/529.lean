import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators Filter

attribute [local instance] Classical.propDecidable

/-- Two points in ℤ^k are adjacent in the integer lattice if their ℓ¹ distance
    is 1 (i.e., they differ by ±1 in exactly one coordinate). -/
def LatticeAdj529 {k : ℕ} (x y : Fin k → ℤ) : Prop :=
  (∑ i : Fin k, |x i - y i|) = 1

/-- The set of self-avoiding walks of n steps in ℤ^k starting at the origin. -/
def selfAvoidingWalks529 (n k : ℕ) : Set (Fin (n + 1) → (Fin k → ℤ)) :=
  {w | w 0 = 0 ∧
    (∀ i : Fin n, LatticeAdj529 (w ⟨i.val, by omega⟩) (w ⟨i.val + 1, by omega⟩)) ∧
    Function.Injective w}

/-- The Euclidean distance of a point in ℤ^k from the origin. -/
noncomputable def euclidDistFromOrigin529 {k : ℕ} (x : Fin k → ℤ) : ℝ :=
  Real.sqrt (∑ i : Fin k, ((x i : ℝ)) ^ 2)

/-- The expected Euclidean distance from the origin of the endpoint of a uniformly
    random self-avoiding walk of n steps in ℤ^k.
    d_k(n) = (1/|SAW(n,k)|) · ∑_{w ∈ SAW(n,k)} ‖w(n)‖₂ -/
noncomputable def expectedSAWDist (n k : ℕ) : ℝ :=
  if h : (selfAvoidingWalks529 n k).Finite then
    (h.toFinset.sum (fun w => euclidDistFromOrigin529 (w ⟨n, by omega⟩))) /
    (h.toFinset.card : ℝ)
  else 0

/--
Erdős Problem #529, Part 1:

Let d_k(n) be the expected distance from the origin after taking n steps of a
uniformly random self-avoiding walk in ℤ^k. Is it true that
  lim_{n→∞} d_2(n)/n^{1/2} = ∞?

That is, in two dimensions, does the expected endpoint distance grow strictly
faster than √n?

Duminil-Copin and Hammond [DuHa13] proved d_2(n) = o(n). It is conjectured
that d_2(n) ~ D·n^{3/4}.
-/
theorem erdos_problem_529_part1 :
    Tendsto (fun n : ℕ => expectedSAWDist n 2 / (n : ℝ) ^ ((1 : ℝ) / 2))
      atTop atTop := sorry

/--
Erdős Problem #529, Part 2:

Is it true that d_k(n) ≪ n^{1/2} for k ≥ 3?

Hara and Slade proved d_k(n) ~ D·n^{1/2} for all k ≥ 5. It is now believed
that this is false for k = 3 and k = 4: the conjectured behavior is
d_3(n) ~ n^ν where ν ≈ 0.59 and d_4(n) ~ D·(log n)^{1/8}·n^{1/2}.
-/
theorem erdos_problem_529_part2 :
    ∀ k : ℕ, k ≥ 3 →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      expectedSAWDist n k ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) := sorry
