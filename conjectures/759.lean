import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #759

The cochromatic number of G, denoted by ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either
a complete graph or an empty graph.

Let z(S_n) be the maximum value of ζ(G) over all graphs G which can be embedded
on S_n, the orientable surface of genus n. Determine the growth rate of z(S_n).

A problem of Erdős and Gimbel [ErGi93]. Gimbel [Gi86] proved that
  √n / log n ≪ z(S_n) ≪ √n.

Solved by Gimbel and Thomassen [GiTh97], who proved
  z(S_n) ≍ √n / log n.
-/

/-- A colouring c : V → Fin k is a cochromatic colouring of G if every colour
    class induces either a complete subgraph or an independent set. -/
def IsCochromaticColouring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G) of a finite graph G: the minimum number of
    colours in a cochromatic colouring. -/
noncomputable def cochromaticNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring G k c}

/-- Embeddability of a finite simple graph on the orientable surface of genus n.
    This is axiomatized since surface topology is not available in Mathlib. -/
def IsEmbeddableOnSurface {m : ℕ} (_ : SimpleGraph (Fin m)) (_ : ℕ) : Prop :=
  sorry

/-- z(S_n): the maximum cochromatic number over all finite graphs embeddable
    on the orientable surface of genus n. -/
noncomputable def maxCochromaticOnSurface (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
    IsEmbeddableOnSurface G n ∧ cochromaticNumber G = k}

/--
Erdős Problem #759, lower bound (Gimbel–Thomassen [GiTh97]):

There exist C > 0 and N₀ such that for all n ≥ N₀,
  z(S_n) ≥ C · √n / log n.
-/
theorem erdos_759_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxCochromaticOnSurface n : ℝ) ≥
        C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) :=
  sorry

/--
Erdős Problem #759, upper bound (Gimbel–Thomassen [GiTh97]):

There exist C > 0 and N₀ such that for all n ≥ N₀,
  z(S_n) ≤ C · √n / log n.
-/
theorem erdos_759_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maxCochromaticOnSurface n : ℝ) ≤
        C * Real.sqrt (n : ℝ) / Real.log (n : ℝ) :=
  sorry

end
