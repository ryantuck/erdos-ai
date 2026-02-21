import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #553

Let R(3,3,n) denote the smallest integer m such that if we 3-colour the edges
of K_m then there is either a monochromatic triangle in one of the first two
colours or a monochromatic K_n in the third colour. Define R(3,n) similarly
but with two colours. Show that

  R(3,3,n) / R(3,n) → ∞

as n → ∞.

A problem of Erdős and Sós. This was solved by Alon and Rödl [AlRo05], who
showed R(3,3,n) ≍ n³(log n)^{O(1)}, recalling that Shearer [Sh83] showed
R(3,n) ≪ n²/log n.
-/

/-- The Ramsey number R(3,n): the minimum N such that every 2-colouring of
    the edges of K_N yields either a monochromatic triangle in colour 1 or
    a monochromatic K_n in colour 2. Equivalently, every simple graph on N
    vertices contains a 3-clique or its complement contains an n-clique. -/
noncomputable def ramseyR3 (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree n}

/-- The Ramsey number R(3,3,n): the minimum N such that every 3-colouring of
    the edges of K_N yields either a monochromatic triangle in one of the
    first two colours or a monochromatic K_n in the third colour.

    A 3-colouring is modelled by two edge-disjoint graphs G₁, G₂ (the first
    two colour classes); the third colour class is the complement (G₁ ⊔ G₂)ᶜ. -/
noncomputable def ramseyR33 (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G₁ G₂ : SimpleGraph (Fin N)),
    Disjoint G₁ G₂ →
    ¬G₁.CliqueFree 3 ∨ ¬G₂.CliqueFree 3 ∨ ¬(G₁ ⊔ G₂)ᶜ.CliqueFree n}

/--
Erdős Problem #553 [ErSo80]:

R(3,3,n) / R(3,n) → ∞ as n → ∞.

Formulated as: for every positive real C, there exists N₀ such that for all
n ≥ N₀ we have R(3,3,n) ≥ C · R(3,n).
-/
theorem erdos_problem_553 :
    ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (ramseyR3 n : ℝ) ≤ (ramseyR33 n : ℝ) :=
  sorry

end
