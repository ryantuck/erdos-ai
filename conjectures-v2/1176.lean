import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

universe u

/-- A graph is properly colorable with at most κ colors (cardinal-valued). -/
def SimpleGraph.CardColorable1176 {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u), #α ≤ κ ∧ Nonempty (G.Coloring α)

/--
Erdős Problem #1176 [Va99,7.93] (OPEN):

Let G be a graph with chromatic number ℵ₁. Is it true that there is a
colouring of the edges with ℵ₁ many colours such that, in any countable
colouring of the vertices, there exists a vertex colour containing all edge
colours?

A problem of Erdős, Galvin, and Hajnal. The consistency of this was proved
by Hajnal and Komjáth.  (The consistency result is metamathematical — a
statement about models of ZFC — and is not formalizable as a plain Mathlib
theorem, so no variant is stated for it.)

Here "a vertex colour containing all edge colours" means: there is a vertex
color class (the set of vertices assigned the same color) such that every edge
color appears on at least one edge whose both endpoints lie in that class.
Neither the edge colouring nor the vertex colouring is required to be proper;
both are arbitrary functions.  Surjectivity of the edge colouring onto its ℵ₁
colours is not assumed but is forced by the conclusion (instantiate the
countable vertex colouring with the constant map to `PUnit`).

"Chromatic number ℵ₁" is encoded exactly: G is properly colorable with ℵ₁
colors but not with countably many.  (The hypothesis ¬CardColorable ℵ₀ alone
would say only "chromatic number ≥ ℵ₁", a strictly larger class of graphs —
whether every graph of uncountable chromatic number contains a subgraph of
chromatic number exactly ℵ₁ is itself a well-known open problem going back to
Galvin, so the two readings are not known to be equivalent.)

Stated as a direct assertion of the "yes" direction of the open question
(raw-file style); the upstream formalization in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1176.lean)
states it as `answer(sorry) ↔ ...` with `G.chromaticCardinal = aleph 1`.

Reference (stub; bibliographic details beyond the booklet unrecoverable
offline):
[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §7.93.

Source: erdosproblems.com/1176 (page edition 24 January 2026, accessed
2026-03-09; status banner OPEN, "cannot be resolved with a finite
computation").  The github.com/teorth/erdosproblems metadata mirror (status
last updated 2026-03-18) agrees: state "not disprovable" (= open, not
resolvable by finite computation), and lists the tags as "set theory,
chromatic number" (the archived page had "set theory | ramsey theory").

https://www.erdosproblems.com/1176
Tags: set theory, ramsey theory (page, 2026-03-09); set theory, chromatic
number (metadata mirror, 2026-03-18)
-/
theorem erdos_problem_1176 :
    ∀ (V : Type) (G : SimpleGraph V),
      ¬G.CardColorable1176 ℵ₀ →
      G.CardColorable1176 ℵ₁ →
      ∃ (EC : Type) (_ : #EC = ℵ₁)
        (edgeColor : G.edgeSet → EC),
        ∀ (VC : Type) (_ : Countable VC)
          (vertexColor : V → VC),
          ∃ (b : VC),
            ∀ (ec : EC), ∃ (e : G.edgeSet),
              edgeColor e = ec ∧
              ∀ v ∈ (e.val : Sym2 V), vertexColor v = b :=
  sorry
