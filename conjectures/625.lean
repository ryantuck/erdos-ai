import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #625

The cochromatic number of G, denoted by ζ(G), is the minimum number of colours
needed to colour the vertices of G such that each colour class induces either a
complete graph or an empty graph. Let χ(G) denote the chromatic number.

If G is a random graph with n vertices and each edge included independently with
probability 1/2, is it true that almost surely
  χ(G) − ζ(G) → ∞
as n → ∞?

A problem of Erdős and Gimbel [ErGi93].
-/

/-- The simple graph on Fin n determined by a Boolean edge matrix. Under G(n, 1/2),
    each Boolean matrix is equally likely, so the fraction of matrices whose graph
    has a property equals the G(n, 1/2)-probability of that property. -/
def toGraph625 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/-- The chromatic number of a simple graph on Fin n: the minimum number of colors k
    such that there exists a proper coloring f : Fin n → Fin k (no two adjacent
    vertices receive the same color). -/
noncomputable def finChromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ f : Fin n → Fin k, ∀ u v, G.Adj u v → f u ≠ f v}

/-- The cochromatic number of a simple graph on Fin n: the minimum number of parts k
    in a coloring f : Fin n → Fin k such that each color class induces either a
    complete subgraph or an independent set. -/
noncomputable def cochromaticNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ f : Fin n → Fin k,
    ∀ c : Fin k,
      (∀ u v, f u = c → f v = c → u ≠ v → G.Adj u v) ∨
      (∀ u v, f u = c → f v = c → u ≠ v → ¬G.Adj u v)}

/--
Erdős Problem #625 [ErGi93]:

In the Erdős–Rényi random graph G(n, 1/2) — the uniform distribution over all
labelled simple graphs on n vertices — the difference χ(G) − ζ(G) tends to infinity
almost surely as n → ∞.

Equivalently: for every M ∈ ℕ and ε > 0, there exists n₀ such that for all n ≥ n₀,
the fraction of graphs on Fin n with χ(G) − ζ(G) ≥ M is at least 1 − ε.
-/
theorem erdos_problem_625 :
    ∀ M : ℕ, ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ((Finset.univ.filter (fun ec : Fin n → Fin n → Bool =>
        finChromaticNumber (toGraph625 ec) - cochromaticNumber (toGraph625 ec) ≥ M)).card : ℝ) ≥
      (1 - ε) * (Fintype.card (Fin n → Fin n → Bool) : ℝ) :=
  sorry

end
