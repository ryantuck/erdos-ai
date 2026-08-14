import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

noncomputable section

namespace Erdos1175

/-!
# Erdős Problem #1175

Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
every graph with chromatic number λ contains a triangle-free subgraph
with chromatic number κ?

A problem from [Va99, 7.92]. Shelah proved that a negative answer is
consistent if κ = λ = ℵ₁.

Status (erdosproblems.com/1175, accessed 2026-02-23, two agreeing log
captures; teorth/erdosproblems metadata mirror, status last update
2026-01-23): OPEN — "This is open, and cannot be resolved with a finite
computation." Since only the *consistency* of a negative answer at
κ = λ = ℵ₁ is known (Shelah), the truth value may depend on the ambient set
theory; the raw statement below asserts the affirmative direction of the
question. (The page capture records "Formalised statement? No"; the mirror's
`formalized` field flipped to "yes" on 2026-05-26, postdating the capture.)

Formalization notes:

- `HasChromaticNumber G κ` is equivalent to "the chromatic number of `G` is
  exactly `κ`": the second conjunct makes `κ` a lower bound on the
  cardinality of every colouring palette, and the first conjunct exhibits a
  palette of cardinality ≤ κ, hence (by the lower bound) exactly κ. The set
  of palette cardinalities is nonempty — `G` is properly coloured by the
  identity colouring into `V` itself — so the minimum is attained (cardinals
  are well-ordered) and `HasChromaticNumber G κ` holds for exactly one `κ`.
- The subgraph relation `H ≤ G` (same vertex set, subset of edges) loses no
  generality against subgraphs on a vertex subset `W ⊆ V`: extending such a
  subgraph by isolated vertices leaves the chromatic number unchanged
  whenever it is ≥ 1 (isolated vertices reuse any existing colour), and
  here it is uncountable.
- `V` ranges over `Type` (universe 0), which realizes every set-sized
  cardinality (every `c : Cardinal.{0}` is `#α` for some `α : Type`), so
  the hypothesis `HasChromaticNumber G mu` is satisfiable for every `mu`
  (e.g. by the complete graph on a type of cardinality `mu`) and the inner
  universal quantifier is never vacuous.
- No degenerate witness trivializes the statement: the chromatic number is
  monotone under `≤`, so any successful `mu` must satisfy `mu ≥ κ`, and by
  Shelah's result `mu = κ` can consistently fail at κ = ℵ₁ — small or equal
  `mu` fail outright rather than vacuously.

Reference: https://www.erdosproblems.com/1175
Tags: set theory, chromatic number

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §7.92. (Site-wide expansion of the key, recovered from the original
  pipeline's fetch of erdosproblems.com/latex/1172; the archived 1175 page
  capture carries the key only as [Va99,7.92]. Stub — no fuller data
  available offline. Shelah's consistency result carries no citation key on
  the source page, so no reference is invented for it.)
-/

/-- The graph G has cardinal chromatic number equal to κ if κ is the minimum
    cardinality of a color set admitting a proper coloring of G:
    - there exists a proper coloring with a color set of cardinality ≤ κ, and
    - every proper coloring uses a color set of cardinality ≥ κ.
    Here G.Coloring α is a graph homomorphism from G to the complete graph on α,
    i.e., a function assigning colors in α to vertices such that adjacent
    vertices receive distinct colors. -/
def HasChromaticNumber {V : Type} (G : SimpleGraph V) (κ : Cardinal.{0}) : Prop :=
  (∃ (α : Type), Cardinal.mk α ≤ κ ∧ Nonempty (G.Coloring α)) ∧
  ∀ (α : Type), Nonempty (G.Coloring α) → κ ≤ Cardinal.mk α

/--
Erdős Problem #1175 [Va99, 7.92] (OPEN):

Let κ be an uncountable cardinal. Must there exist a cardinal λ such that
every graph with chromatic number λ contains a triangle-free subgraph
with chromatic number κ?

Here HasChromaticNumber G κ means κ is the minimum cardinality of a color set
admitting a proper coloring of G. Triangle-free means G.CliqueFree 3 (no
3-clique, i.e., no triangle). The subgraph relation H ≤ G holds when every
edge of H is also an edge of G. The binder `mu` plays the role of the
problem's λ (`lambda` is reserved in Lean).

Shelah proved that a negative answer is consistent if κ = λ = ℵ₁. The source
poses this as a yes/no question; this raw statement asserts the affirmative
direction. Since only Shelah's consistency result is known, the truth value
may depend on the ambient set theory.
-/
theorem erdos_problem_1175 :
    ∀ κ : Cardinal.{0}, aleph 1 ≤ κ →
    ∃ mu : Cardinal.{0},
      ∀ (V : Type) (G : SimpleGraph V), HasChromaticNumber G mu →
        ∃ H : SimpleGraph V, H ≤ G ∧ H.CliqueFree 3 ∧ HasChromaticNumber H κ :=
  sorry

end Erdos1175

end
