import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #760

The cochromatic number of G, denoted by ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either
a complete graph or an empty graph.

If G is a graph with chromatic number χ(G) = m then must G contain a subgraph H
with ζ(H) ≫ m / log m?

A problem of Erdős and Gimbel [ErGi93], who proved that there must exist a
subgraph H with ζ(H) ≫ (m / log m)^{1/2}. The proposed bound would be best
possible, as shown by taking G to be a complete graph.

The answer is yes, proved by Alon, Krivelevich, and Sudakov [AKS97].

Tags: graph theory, chromatic number
-/

/-- A colouring c : V → Fin k is a cochromatic colouring of G if every colour
    class induces either a complete subgraph or an independent set. -/
def IsCochromaticColouring760 {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (c : V → Fin k) : Prop :=
  ∀ i : Fin k,
    (∀ u v, c u = i → c v = i → u ≠ v → G.Adj u v) ∨
    (∀ u v, c u = i → c v = i → u ≠ v → ¬G.Adj u v)

/-- The cochromatic number ζ(G) of a finite graph G: the minimum number of
    colours in a cochromatic colouring. -/
noncomputable def cochromaticNumber760 {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ c : V → Fin k, IsCochromaticColouring760 G k c}

/--
**Erdős Problem #760** (PROVED, Alon–Krivelevich–Sudakov [AKS97]):

There exists a constant C > 0 such that for every graph G with sufficiently
large chromatic number m = χ(G), there exists an induced subgraph H of G with
cochromatic number ζ(H) ≥ C · m / log m.
-/
theorem erdos_problem_760 :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber.toNat ≥ N₀ →
        ∃ (S : Finset (Fin n)),
          (cochromaticNumber760 (G.induce (↑S : Set (Fin n))) : ℝ) ≥
            C * (G.chromaticNumber.toNat : ℝ) / Real.log (G.chromaticNumber.toNat : ℝ) :=
  sorry

end
