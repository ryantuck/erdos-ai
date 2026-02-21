import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #182

Let k ≥ 3. What is the maximum number of edges that a graph on n vertices can
contain if it does not have a k-regular subgraph? Is it ≪ n^{1+o(1)}?

Asked by Erdős and Sauer. Resolved by Janzer and Sudakov [JaSu23], who proved
that there exists some C = C(k) > 0 such that any graph on n vertices with at
least C·n·log(log(n)) edges contains a k-regular subgraph.

A construction due to Pyber, Rödl, and Szemerédi [PRS95] shows that this
bound is best possible up to the value of the constant C(k).
-/

/-- G contains a k-regular subgraph: there exists a nonempty finite graph H that
    is k-regular (every vertex has degree exactly k) and admits an injective
    graph homomorphism into G. -/
def containsKRegularSubgraph182 {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (U : Type) (fU : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (dH : DecidableRel H.Adj),
    haveI := fU; haveI := dH;
    (∀ v : U, H.degree v = k) ∧
    ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #182 (Erdős-Sauer conjecture) [Er75, Er81]:

For every k ≥ 3, there exists a constant C > 0 such that for all sufficiently
large n, every simple graph on n vertices with at least C · n · log(log(n))
edges contains a k-regular subgraph.

Proved by Janzer and Sudakov [JaSu23].
-/
theorem erdos_problem_182 :
    ∀ k : ℕ, 3 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ), n₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) * Real.log (Real.log (n : ℝ)) →
      containsKRegularSubgraph182 G k :=
  sorry

end
