import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #799

The list chromatic number χ_L(G) is defined to be the minimal k such that for any
assignment of a list of k colours to each vertex of G (perhaps different lists for
different vertices) a colouring of each vertex by a colour on its list can be chosen
such that adjacent vertices receive distinct colours.

Is it true that χ_L(G) = o(n) for almost all graphs on n vertices?

A problem of Erdős, Rubin and Taylor [ERT80]. The answer is yes: Alon [Al92] proved
that the random graph on n vertices with edge probability 1/2 has
χ_L(G) ≪ (log log n / log n) · n almost surely. Alon, Krivelevich, and Sudakov [AKS99]
improved this to χ_L(G) ≍ n / log n almost surely.

https://www.erdosproblems.com/799

Tags: graph theory, chromatic number
-/

/-- A proper list coloring of G with respect to a list assignment L : V → Finset ℕ
    is a function f : V → ℕ such that f(v) ∈ L(v) for all v, and f(u) ≠ f(v)
    whenever u and v are adjacent. -/
def Erdos799.IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph G is k-choosable (k-list-colorable) if for every list assignment L
    where each vertex receives a list of at least k colors, there exists a
    proper list coloring. -/
def Erdos799.IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, Erdos799.IsProperListColoring G L f

/-- The simple graph on Fin n determined by a Boolean edge predicate.
    Only the upper-triangle entries ec (min u v) (max u v) for u ≠ v are read. -/
def Erdos799.toGraph {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The fraction of all labeled graphs on n vertices satisfying property P.
    Each graph is encoded by a Boolean edge predicate; the graph is read
    from the upper triangle, so every graph has equal weight. -/
noncomputable def Erdos799.graphFraction (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter
    (fun ec => P (Erdos799.toGraph ec))).card /
  ((Finset.univ : Finset (Fin n → Fin n → Bool)).card : ℝ)

/--
Erdős Problem #799 [ERT80]:

For almost all graphs on n vertices, χ_L(G) = o(n).

Formally: for every ε > 0 and δ > 0, there exists n₀ such that for all n ≥ n₀
and all k ≥ εn, the fraction of labeled graphs on n vertices that are k-choosable
is at least 1 - δ. (This is equivalent to asking that ⌈εn⌉-choosability holds for
almost all graphs, since choosability is monotone in k.)

Proved by Alon [Al92] and strengthened by Alon, Krivelevich, and Sudakov [AKS99].
-/
theorem erdos_problem_799 :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ k : ℕ, (k : ℝ) ≥ ε * (n : ℝ) →
        Erdos799.graphFraction n (fun G => Erdos799.IsChoosable G k) ≥ 1 - δ :=
  sorry

end
