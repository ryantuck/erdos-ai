import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-!
# Erdős Problem #159

There exists some constant c > 0 such that R(C₄, Kₙ) ≪ n^{2-c}.

Here R(C₄, Kₙ) is the graph Ramsey number: the minimum N such that every
simple graph on N vertices contains a copy of C₄ as a subgraph, or whose
complement contains a copy of Kₙ (equivalently, G has an independent set
of size n).

Current bounds: n^{3/2}/(log n)^{3/2} ≪ R(C₄, Kₙ) ≪ n²/(log n)².
-/

/-- An injective graph homomorphism from H to G witnesses that G contains
    a subgraph isomorphic to H. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The 4-cycle C₄: vertices Fin 4, with i adjacent to j iff they are
    consecutive modulo 4 (i.e., the edges are 0–1, 1–2, 2–3, 3–0). -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

/-- The graph Ramsey number R(C₄, Kₙ): the minimum N such that every simple
    graph G on N vertices either contains a copy of C₄ as a subgraph, or the
    complement Gᶜ contains a copy of Kₙ (i.e., G has an independent set of
    size n). -/
noncomputable def ramseyC4Kn (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin n))}

/--
Erdős Conjecture (Problem #159) [Er81, Er84d]:

There exists a constant c > 0 such that R(C₄, Kₙ) ≪ n^{2-c}, i.e.,
R(C₄, Kₙ) = O(n^{2-c}) as n → ∞.

The Ramsey number R(C₄, Kₙ) is the minimum N such that every 2-colouring
of the edges of K_N contains a monochromatic C₄ in one colour or a
monochromatic Kₙ in the other colour.

The current bounds are:
  n^{3/2} / (log n)^{3/2} ≪ R(C₄, Kₙ) ≪ n² / (log n)²,
where the upper bound is due to Szemerédi [EFRS78] and the lower bound
to Spencer [Sp77]. Improving the upper bound to n^{2-c} for any fixed
c > 0 remains open.
-/
theorem erdos_problem_159 :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c) :=
  sorry
