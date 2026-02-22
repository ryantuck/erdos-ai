import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #956

If C, D ⊆ ℝ² then the distance between C and D is defined by
  δ(C, D) = inf { ‖c - d‖ | c ∈ C, d ∈ D }.

Let h(n) be the maximal number of unit distances between disjoint convex
translates. That is, the maximal m such that there is a compact convex set
C ⊂ ℝ² and a set X of size n such that all (C + x)_{x ∈ X} are disjoint
and there are m pairs x₁, x₂ ∈ X such that δ(C + x₁, C + x₂) = 1.

Prove that there exists a constant c > 0 such that h(n) > n^{1+c} for all
large n.

A problem of Erdős and Pach [ErPa90], who proved that h(n) ≪ n^{4/3}.
It is trivial that h(n) ≥ f(n) where f(n) is the maximal number of unit
distances determined by n points in ℝ².

Tags: geometry | distances | convex
-/

/-- The distance between two subsets of a metric space:
    δ(C, D) = inf { dist c d | c ∈ C, d ∈ D }. -/
noncomputable def setDist956 {α : Type*} [PseudoMetricSpace α]
    (C D : Set α) : ℝ :=
  sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = dist c d}

/-- The translate of a set C by a vector x: C + x = { c + x | c ∈ C }. -/
def translate956 {α : Type*} [Add α] (C : Set α) (x : α) : Set α :=
  (· + x) '' C

/--
**Erdős Problem #956** [ErPa90]:

There exists a constant c > 0 such that for all sufficiently large n,
one can find a compact convex set C ⊂ ℝ² and n translation vectors whose
translates of C are pairwise disjoint with more than n^{1+c} pairs at
unit set-distance.
-/
theorem erdos_problem_956 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ (C : Set (EuclideanSpace ℝ (Fin 2))),
        IsCompact C ∧ Convex ℝ C ∧ C.Nonempty ∧
      ∃ (X : Finset (EuclideanSpace ℝ (Fin 2))),
        X.card = n ∧
        (∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ →
          Disjoint (translate956 C x₁) (translate956 C x₂)) ∧
      ∃ (P : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
        (∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧
          setDist956 (translate956 C p.1) (translate956 C p.2) = 1) ∧
        (∀ p ∈ P, (p.2, p.1) ∉ P) ∧
        ((P.card : ℝ) > (n : ℝ) ^ ((1 : ℝ) + c)) :=
  sorry

/--
**Erdős Problem #956, upper bound** [ErPa90]:

h(n) ≪ n^{4/3}. For any compact convex set C and n translations with
pairwise disjoint translates, the number of pairs at unit set-distance
is O(n^{4/3}).
-/
theorem erdos_problem_956_upper_bound :
    ∃ K : ℝ, K > 0 ∧
    ∀ (C : Set (EuclideanSpace ℝ (Fin 2))),
      IsCompact C → Convex ℝ C → C.Nonempty →
    ∀ (X : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ ≠ x₂ →
        Disjoint (translate956 C x₁) (translate956 C x₂)) →
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
      (∀ p ∈ P, p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧
        setDist956 (translate956 C p.1) (translate956 C p.2) = 1) →
      (∀ p ∈ P, (p.2, p.1) ∉ P) →
      (P.card : ℝ) ≤ K * (X.card : ℝ) ^ ((4 : ℝ) / 3) :=
  sorry

end
