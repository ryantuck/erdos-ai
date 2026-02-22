import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1024

Let f(n) be such that every 3-uniform linear hypergraph on n vertices contains
an independent set on f(n) vertices. Estimate f(n).

A hypergraph is linear if |A ∩ B| ≤ 1 for all edges A and B. An independent
set of vertices is one which contains no edges. A 3-uniform linear hypergraph
is sometimes called a partial Steiner triple system.

Erdős proved n^{1/2} ≪ f(n) ≪ n^{2/3}. Phelps and Rödl [PhRo86] proved
f(n) ≍ (n log n)^{1/2}.
-/

/-- A 3-uniform hypergraph on `Fin n`: a family of 3-element subsets. -/
structure Hypergraph3Uniform (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph is *linear* if any two distinct edges share
    at most one vertex. -/
def Hypergraph3Uniform.IsLinear {n : ℕ} (H : Hypergraph3Uniform n) : Prop :=
  ∀ e₁ ∈ H.edges, ∀ e₂ ∈ H.edges, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1

/-- A set `S` of vertices is *independent* in `H` if no edge of `H` is
    contained in `S`. -/
def Hypergraph3Uniform.IsIndependent {n : ℕ} (H : Hypergraph3Uniform n)
    (S : Finset (Fin n)) : Prop :=
  ∀ e ∈ H.edges, ¬(e ⊆ S)

/-- The independence number of `H`: the maximum size of an independent set. -/
noncomputable def Hypergraph3Uniform.independenceNumber {n : ℕ}
    (H : Hypergraph3Uniform n) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n), H.IsIndependent S ∧ S.card = k}

/-- `linearHypergraphIndNum n` is the minimum independence number over all
    3-uniform linear hypergraphs on `n` vertices, i.e. the largest `f` such
    that every such hypergraph has an independent set of size at least `f`. -/
noncomputable def linearHypergraphIndNum (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ H : Hypergraph3Uniform n, H.IsLinear ∧
    H.independenceNumber = k}

/--
Erdős Problem #1024 (solved by Phelps–Rödl [PhRo86]):

f(n) ≍ (n log n)^{1/2}, where f(n) is the minimum independence number over
all 3-uniform linear hypergraphs on n vertices.

There exist constants C₁, C₂ > 0 and N₀ such that for all n ≥ N₀,
  C₁ · √(n · log n) ≤ f(n) ≤ C₂ · √(n · log n).
-/
theorem erdos_problem_1024 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * Real.sqrt (↑n * Real.log ↑n) ≤ ↑(linearHypergraphIndNum n) ∧
      ↑(linearHypergraphIndNum n) ≤ C₂ * Real.sqrt (↑n * Real.log ↑n) :=
  sorry

end
