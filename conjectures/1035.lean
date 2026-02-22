import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #1035

Is there a constant $c > 0$ such that every graph on $2^n$ vertices with
minimum degree $> (1 - c) \cdot 2^n$ contains the $n$-dimensional hypercube $Q_n$?

A problem of Erdős [Er93, p.345].
-/

/-- The n-dimensional hypercube graph Q_n: vertices are functions Fin n → Bool,
    and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph1035 (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := ⟨fun v h => h.1 rfl⟩

/-- An injective graph homomorphism from H to G: G contains a copy of H as a subgraph. -/
def containsSubgraph1035 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Conjecture (Problem #1035) [Er93, p.345]:

Is there a constant c > 0 such that every graph on 2^n vertices with
minimum degree > (1 - c) · 2^n contains the n-dimensional hypercube Q_n?

Formulated as: there exists c > 0 such that for all n and for every graph G
on 2^n vertices, if every vertex has degree > (1 - c) · 2^n, then G contains
a copy of Q_n as a subgraph.
-/
theorem erdos_problem_1035 :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ,
    ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
      (∀ v : Fin (2 ^ n),
        ((Finset.univ.filter (fun w => G.Adj v w)).card : ℝ) > (1 - c) * (2 ^ n : ℝ)) →
      containsSubgraph1035 G (hypercubeGraph1035 n) :=
  sorry

end
