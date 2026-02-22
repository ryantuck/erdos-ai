import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

attribute [local instance] Classical.propDecidable

/-!
# Erdős Problem #1088

Let f_d(n) be the minimal m such that any set of m points in ℝ^d contains
a set of n points such that any two determined distances are distinct.
Estimate f_d(n). In particular, is it true that, for fixed n ≥ 3,
  f_d(n) = 2^{o(d)}?

A problem of Erdős [Er75f]. It is easy to prove that f_d(n) ≤ n^{O_d(1)}.
Erdős claimed that he and Straus proved f_d(n) ≤ c_n^d for some constant c_n > 0.

When d = 1, f_1(n) ≍ n². When n = 3, f_d(3) = d²/2 + O(d).
-/

noncomputable section

/-- A finite set of points in a metric space has all pairwise distances
    distinct if no two distinct unordered pairs determine the same distance:
    whenever dist(a, b) = dist(c, d) with a ≠ b and c ≠ d, the pairs
    {a, b} and {c, d} must coincide. -/
def allPairwiseDistinctDists {α : Type*} [MetricSpace α]
    (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≠ b → c ≠ d → dist a b = dist c d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- f_d(n) is the minimal m such that any set of at least m points in ℝ^d
    contains a subset of n points with all pairwise distances distinct. -/
noncomputable def erdos_f (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
    S.card ≥ m →
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      T ⊆ S ∧ T.card = n ∧ allPairwiseDistinctDists T}

/--
Erdős Problem #1088 [Er75f]:

For fixed n ≥ 3, f_d(n) = 2^{o(d)} as d → ∞. That is, for every ε > 0,
there exists D₀ such that for all d ≥ D₀, f_d(n) ≤ 2^{ε · d}.
-/
theorem erdos_problem_1088 (n : ℕ) (hn : n ≥ 3) :
    ∀ ε : ℝ, ε > 0 →
    ∃ D₀ : ℕ, ∀ d : ℕ, d ≥ D₀ →
      (erdos_f d n : ℝ) ≤ (2 : ℝ) ^ (ε * (d : ℝ)) :=
  sorry

end
