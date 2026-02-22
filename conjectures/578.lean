import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #578

If G is a random graph on 2^d vertices, including each edge with probability 1/2,
then G almost surely contains a copy of Q_d (the d-dimensional hypercube with 2^d
vertices and d·2^{d-1} many edges).

A conjecture of Erdős and Bollobás [Er90c]. Solved by Riordan [Ri00], who in fact
proved this with any edge-probability > 1/4.
-/

/-- The d-dimensional hypercube graph Q_d. Vertices are functions Fin d → Bool
    (binary strings of length d). Two vertices are adjacent iff they differ in
    exactly one coordinate. -/
def hypercubeGraph (d : ℕ) : SimpleGraph (Fin d → Bool) where
  Adj u v := (Finset.univ.filter fun i => u i ≠ v i).card = 1
  symm := by
    intro u v h
    have heq : (Finset.univ.filter fun i : Fin d => v i ≠ u i) =
               (Finset.univ.filter fun i : Fin d => u i ≠ v i) := by
      ext i; simp [ne_comm]
    rw [heq]; exact h
  loopless := ⟨fun v h => by
    have : (Finset.univ.filter fun i : Fin d => v i ≠ v i) = ∅ := by
      ext i; simp
    rw [this] at h; exact absurd h (by norm_num)⟩

/-- The simple graph on Fin n determined by a Boolean matrix. Only values at
    (min u v, max u v) matter; this ensures symmetry. Under G(n, 1/2), each
    Boolean matrix is equally likely, and the fraction of matrices whose graph
    has a property equals the probability that G(n, 1/2) has that property. -/
def toGraph578 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/--
Erdős Problem #578 [Er90c]:

In the Erdős–Rényi random graph G(2^d, 1/2) — the uniform distribution over all
labelled simple graphs on 2^d vertices — the probability that G contains a copy
of Q_d (the d-dimensional hypercube) tends to 1 as d → ∞.

A copy of Q_d in G means an injective map f from the vertices of Q_d to the
vertices of G such that adjacent vertices in Q_d map to adjacent vertices in G.

Equivalently: for every ε > 0 there exists d₀ such that for all d ≥ d₀ the
fraction of Boolean matrices on Fin (2^d) whose graph contains Q_d is ≥ 1 − ε.
-/
theorem erdos_problem_578 :
    ∀ ε : ℝ, ε > 0 →
    ∃ d₀ : ℕ, ∀ d : ℕ, d ≥ d₀ →
      ((Finset.univ.filter (fun ec : Fin (2 ^ d) → Fin (2 ^ d) → Bool =>
        ∃ f : (Fin d → Bool) → Fin (2 ^ d),
          Function.Injective f ∧
          ∀ u v, (hypercubeGraph d).Adj u v →
            (toGraph578 ec).Adj (f u) (f v))).card : ℝ) ≥
      (1 - ε) * (Fintype.card (Fin (2 ^ d) → Fin (2 ^ d) → Bool) : ℝ) :=
  sorry

end
