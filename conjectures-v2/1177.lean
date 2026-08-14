import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Finset.Card

open Cardinal

noncomputable section

namespace Erdos1177

/-!
# Erdős Problem #1177

Let G be a finite 3-uniform hypergraph, and let F_G(κ) denote the collection of
3-uniform hypergraphs with chromatic number κ not containing G.

If F_G(ℵ₁) is not empty then there exists X ∈ F_G(ℵ₁) of cardinality at most 2^(2^ℵ₀).

If both F_G(ℵ₁) and F_H(ℵ₁) are non-empty then F_G(ℵ₁) ∩ F_H(ℵ₁) is non-empty.

If κ, λ are uncountable cardinals and F_G(κ) is non-empty then F_G(λ) is non-empty.

A problem of Erdős, Galvin, and Hajnal.

Status: OPEN (erdosproblems.com/1177, page edition 23 January 2026, accessed
2026-02-23; cross-checked against the teorth/erdosproblems metadata mirror,
status "open", last update 2026-01-23). The page lists no partial results,
no related OEIS sequences, and no cross-referenced problems.

References:

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §7.94.
  (Bibliographic data recovered from sibling formalizations carrying the same
  key; the erdosproblems.com/latex/1177 page itself carries no bibliography.)

Tags: set theory, chromatic number, hypergraphs
-/

/-- A proper coloring of a 3-uniform hypergraph with vertex type V using colors from α
    is a function c : V → α such that no hyperedge is monochromatic: for every edge e
    there exist two vertices in e assigned different colors. -/
def IsProperColoring3 {V α : Type*} (edges : Set (Finset V)) (c : V → α) : Prop :=
  ∀ e ∈ edges, ∃ v ∈ e, ∃ w ∈ e, c v ≠ c w

/-- A 3-uniform hypergraph (on vertex type V, with edge set edges) has cardinal chromatic
    number κ if κ is the least cardinality of a color set admitting a proper coloring:
    - there exists a proper coloring with a color set of cardinality ≤ κ, and
    - every proper coloring requires a color set of cardinality ≥ κ. -/
def HasChromaticNumber3 {V : Type} (edges : Set (Finset V)) (κ : Cardinal.{0}) : Prop :=
  (∃ (α : Type), #α ≤ κ ∧ ∃ c : V → α, IsProperColoring3 edges c) ∧
  ∀ (α : Type), (∃ c : V → α, IsProperColoring3 edges c) → κ ≤ #α

/-- H is G-free if there is no injective map f : VG → VH sending every edge of G to an
    edge of H (i.e., G does not embed as a sub-hypergraph of H). Each edge of G maps to
    an edge of H via f when the image of the edge under f equals an edge of H as a set.

    Note the degenerate case: if G has no edges, `IsFreeOf` reduces to the assertion
    that no injective map VG → VH exists at all, so any H with at least |VG| vertices
    *contains* the edgeless G. Consequently F_G(ℵ₁) is empty for edgeless G (a
    hypergraph of uncountable chromatic number has uncountably many vertices), and the
    problem statements below are vacuously true there — consistent with the source,
    which only concerns G with edges. -/
def IsFreeOf {VG VH : Type*} (edgesG : Set (Finset VG)) (edgesH : Set (Finset VH)) : Prop :=
  ¬ ∃ f : VG → VH, Function.Injective f ∧
    ∀ e ∈ edgesG, ∃ e' ∈ edgesH, (↑e' : Set VH) = f '' (↑e : Set VG)

/--
Erdős Problem #1177, Part 1 [Va99, 7.94]:

Let G be a finite 3-uniform hypergraph. If F_G(ℵ₁) is non-empty (i.e., there exists
a G-free 3-uniform hypergraph with chromatic number ℵ₁), then there exists X ∈ F_G(ℵ₁)
with vertex set of cardinality at most 2^(2^ℵ₀).

Here IsFreeOf edgesG edgesH means H contains no sub-hypergraph isomorphic to G,
and HasChromaticNumber3 edgesH κ means κ is the minimum cardinality of a color set
for a proper (non-monochromatic-edge) coloring of H.

(Finiteness of the edge set of G follows from `[Fintype VG]`, since a finite vertex
type carries only finitely many potential edges.)

A problem of Erdős, Galvin, and Hajnal.
-/
theorem erdos_problem_1177a
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (hG : ∀ e ∈ edgesG, e.card = 3)
    (h : ∃ (VH : Type) (edgesH : Set (Finset VH)),
      (∀ e ∈ edgesH, e.card = 3) ∧
      HasChromaticNumber3 edgesH (aleph 1) ∧
      IsFreeOf edgesG edgesH) :
    ∃ (VH : Type) (edgesH : Set (Finset VH)),
      (∀ e ∈ edgesH, e.card = 3) ∧
      HasChromaticNumber3 edgesH (aleph 1) ∧
      IsFreeOf edgesG edgesH ∧
      #VH ≤ (2 : Cardinal.{0}) ^ (2 : Cardinal.{0}) ^ aleph 0 :=
  sorry

/--
Erdős Problem #1177, Part 2 [Va99, 7.94]:

Let G and H be finite 3-uniform hypergraphs. If F_G(ℵ₁) and F_H(ℵ₁) are both
non-empty, then F_G(ℵ₁) ∩ F_H(ℵ₁) is non-empty: there exists a 3-uniform hypergraph
with chromatic number ℵ₁ that contains neither G nor H as a sub-hypergraph.

A problem of Erdős, Galvin, and Hajnal.
-/
theorem erdos_problem_1177b
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (hG : ∀ e ∈ edgesG, e.card = 3)
    {VH : Type} [Fintype VH] (edgesH : Set (Finset VH))
    (hH : ∀ e ∈ edgesH, e.card = 3)
    (hFG : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesG edgesW)
    (hFH : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesH edgesW) :
    ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW (aleph 1) ∧
      IsFreeOf edgesG edgesW ∧ IsFreeOf edgesH edgesW :=
  sorry

/--
Erdős Problem #1177, Part 3 [Va99, 7.94]:

Let G be a finite 3-uniform hypergraph. If κ and μ are uncountable cardinals (both ≥ ℵ₁)
and F_G(κ) is non-empty, then F_G(μ) is non-empty: the existence of a G-free 3-uniform
hypergraph with chromatic number κ implies the existence of one with chromatic number μ.

(The source writes λ for the second cardinal; μ is used here to avoid Lean's λ keyword.
"Uncountable" is encoded as ℵ₁ ≤ κ, equivalent under choice.)

A problem of Erdős, Galvin, and Hajnal.
-/
theorem erdos_problem_1177c
    {VG : Type} [Fintype VG] (edgesG : Set (Finset VG))
    (hG : ∀ e ∈ edgesG, e.card = 3)
    (κ μ : Cardinal.{0}) (hκ : aleph 1 ≤ κ) (hμ : aleph 1 ≤ μ)
    (h : ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW κ ∧
      IsFreeOf edgesG edgesW) :
    ∃ (W : Type) (edgesW : Set (Finset W)),
      (∀ e ∈ edgesW, e.card = 3) ∧
      HasChromaticNumber3 edgesW μ ∧
      IsFreeOf edgesG edgesW :=
  sorry

end Erdos1177

end
