import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1042

Let F ⊂ ℂ be a closed set of transfinite diameter 1 which is not contained in
any closed disc of radius 1. If f(z) = ∏(z - zᵢ) ∈ ℂ[x] with all zᵢ ∈ F,
can {z : |f(z)| < 1} have n connected components?

If the transfinite diameter of F is < 1 then must this set have at most (1-c)n
connected components, where c > 0 depends only on F?

A problem of Erdős, Herzog, and Piranian [EHP58, p.139].

Solved by Ghosh and Ramachandran [GhRa24], who proved that:
- If 0 < d < 1, the set has at most (1-c)n connected components for some c > 0
  depending on F.
- If d ≤ 1/4 and F is connected, the set has only one connected component.
- There exist closed sets F with d = 1 such that, for infinitely many n, the
  set can have n connected components.
-/

/-- The product of pairwise distances ∏_{i<j} ‖z i - z j‖ for a tuple of
    complex numbers. -/
noncomputable def pairwiseDistProd1042 {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The n-th transfinite diameter of F ⊆ ℂ:
    d_n(F) = sup_{z₁,...,zₙ ∈ F} (∏_{i<j} |zᵢ - zⱼ|)^(2/(n(n-1))). -/
noncomputable def nthTransfiniteDiam1042 (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd1042 z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of F ⊆ ℂ:
    ρ(F) = lim_{n → ∞} d_n(F). -/
noncomputable def transfiniteDiameter1042 (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam1042 F n))

/-- The sublevel set {z : ‖∏ᵢ(z - zᵢ)‖ < 1} of a monic polynomial with
    given roots. -/
def sublevelSet1042 {n : ℕ} (z : Fin n → ℂ) : Set ℂ :=
  {w : ℂ | ‖(univ : Finset (Fin n)).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem #1042, existence [GhRa24]:

There exists a closed set F ⊂ ℂ with transfinite diameter 1, not contained in
any closed disc of radius 1, and for infinitely many n there exist z₁,...,zₙ ∈ F
such that {z : |∏(z - zᵢ)| < 1} has exactly n connected components.
-/
theorem erdos_problem_1042_existence :
    ∃ (F : Set ℂ), IsClosed F ∧ transfiniteDiameter1042 F = 1 ∧
      (¬∃ c : ℂ, F ⊆ Metric.closedBall c 1) ∧
      Set.Infinite {n : ℕ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
        Nat.card (ConnectedComponents ↥(sublevelSet1042 z)) = n} :=
  sorry

/--
Erdős Problem #1042, upper bound [GhRa24]:

If F ⊂ ℂ is closed with 0 < transfinite diameter < 1, then there exists c > 0
(depending on F) such that for all n and all z₁,...,zₙ ∈ F, the number of
connected components of {z : |∏(z - zᵢ)| < 1} is at most (1-c)·n.
-/
theorem erdos_problem_1042_upper_bound (F : Set ℂ) (hF : IsClosed F)
    (hd_pos : transfiniteDiameter1042 F > 0) (hd_lt : transfiniteDiameter1042 F < 1) :
    ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, z i ∈ F) →
      (Nat.card (ConnectedComponents ↥(sublevelSet1042 z)) : ℝ) ≤ (1 - c) * n :=
  sorry

end
