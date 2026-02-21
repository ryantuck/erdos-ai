import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #180

If F is a finite set of finite graphs then ex(n; F) is the maximum number of edges
a graph on n vertices can have without containing any subgraphs from F. Note that it
is trivial that ex(n; F) ≤ ex(n; G) for every G ∈ F.

Is it true that, for every F, there exists G ∈ F such that
  ex(n; G) ≪_F ex(n; F)?

That is, there exists a constant C (depending on F) such that
  ex(n; G) ≤ C · ex(n; F) for all n ≥ 1.

A problem of Erdős and Simonovits [ErSi82].

Note: Hunter has provided a folklore counterexample: if F = {H₁, H₂} where H₁ is a
star and H₂ is a matching (both with at least two edges), then ex(n; F) ≪ 1 but
ex(n; Hᵢ) ≍ n for 1 ≤ i ≤ 2. The conjecture may still hold for all other F.
-/

/-- An injective graph homomorphism from H to G: G contains a copy of H as a subgraph. -/
def containsSubgraph180 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber180 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph180 F H ∧ F.edgeFinset.card = m}

/-- The Turán number for a family ex(n; F): the maximum number of edges in a simple
    graph on n vertices that contains no copy of any member of the family F as a
    subgraph. The family is given as a function from a finite index type ι to finite
    graphs SimpleGraph (Fin (k i)). -/
noncomputable def turanNumberFamily180
    {ι : Type*} [Fintype ι]
    {k : ι → ℕ} (H : (i : ι) → SimpleGraph (Fin (k i))) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ (∀ i : ι, ¬containsSubgraph180 F (H i)) ∧ F.edgeFinset.card = m}

/--
Erdős Conjecture (Problem #180) [ErSi82]:

If F is a finite set of finite graphs, then there exists some G ∈ F such that
  ex(n; G) ≤ C · ex(n; F)
for some constant C depending on F and all n ≥ 1.

In other words, the Turán number of some individual member of the family is always
within a constant factor of the Turán number of the whole family.

Note: This has been disproved by a folklore counterexample (Hunter): if F = {H₁, H₂}
where H₁ is a star and H₂ is a matching (both with ≥ 2 edges), then ex(n; F) ≪ 1
but ex(n; Hᵢ) ≍ n. The conjecture may still hold for other families.
-/
theorem erdos_problem_180 :
    ∀ (ι : Type) [Fintype ι] [Nonempty ι]
      (k : ι → ℕ) (H : (i : ι) → SimpleGraph (Fin (k i))),
    ∃ i : ι,
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (turanNumber180 (H i) n : ℝ) ≤ C * (turanNumberFamily180 H n : ℝ) :=
  sorry

end
