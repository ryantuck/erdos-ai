import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #181

Let Q_n be the n-dimensional hypercube graph (so that Q_n has 2^n vertices and
n·2^{n-1} edges). Prove that R(Q_n) ≪ 2^n.

Here R(Q_n) is the diagonal Ramsey number: the minimum N such that every
2-colouring of the edges of K_N contains a monochromatic copy of Q_n.

Conjectured by Burr and Erdős [BuEr75].
-/

/-- The n-dimensional hypercube graph Q_n: vertices are functions Fin n → Bool,
    and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

/-- An injective graph homomorphism from H to G: G contains a (not necessarily
    induced) copy of H as a subgraph. -/
def containsCopy181 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The diagonal Ramsey number R(H): the minimum N such that for every simple
    graph G on Fin N, either G or Gᶜ contains a copy of H. -/
noncomputable def ramseyDiag181 {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsCopy181 G H ∨ containsCopy181 Gᶜ H}

/--
Erdős Conjecture (Problem #181) [BuEr75]:

Let Q_n be the n-dimensional hypercube graph. Prove that
  R(Q_n) ≪ 2^n,
i.e., there exists a constant C > 0 such that R(Q_n) ≤ C · 2^n for all n ≥ 1.
-/
theorem erdos_problem_181 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag181 (hypercubeGraph n) : ℝ) ≤ C * (2 ^ n : ℝ) :=
  sorry

end
