import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

noncomputable section

namespace Erdos1174

/-!
# Erdős Problem #1174

Does there exist a graph G with no K_4 such that every edge colouring of G
with countably many colours contains a monochromatic K_3?

Does there exist a graph G with no K_{ℵ_1} such that every edge colouring of G
with countably many colours contains a monochromatic K_{ℵ_0}?

A problem of Erdős and Hajnal [Va99, 7.91]. Shelah proved that a graph with
either property can consistently exist.

Status (erdosproblems.com/1174, accessed 2026-02-23 and 2026-03-15, two
agreeing captures; teorth/erdosproblems metadata mirror, last update
2026-03-19): OPEN — "This is open, and cannot be resolved with a finite
computation." Since only the *consistency* of a positive answer is known
(Shelah), each part may depend on the ambient set theory; the raw statements
below assert the affirmative direction of each question.

Formalization notes:

- Edge colourings are encoded as total symmetric functions `col : V → V → ℕ`.
  This is equivalent to colouring the edge set of `G` from a countable
  palette: every edge colouring extends to a total symmetric function (colour
  non-edges and the diagonal arbitrarily), and the monochromatic conclusion
  only inspects pairs of distinct vertices inside a clique of `G`, which are
  edges.
- "No K_{ℵ₁}" is encoded as "no clique of cardinality ≥ ℵ₁"; this is
  equivalent to "no clique of cardinality exactly ℵ₁" since any subset of a
  clique is a clique. Likewise a clique of cardinality ≥ ℵ₀ is exactly an
  infinite clique, i.e. contains a K_{ℵ₀}. Similarly, "no K₄" via
  `¬ IsNClique 4` also excludes all larger finite cliques.
- `V` ranges over `Type` (universe 0), which realizes every set-sized
  cardinality (every `c : Cardinal.{0}` is `#α` for some `α : Type`), so
  this is no restriction. Any witness for either part must have uncountably
  many edges: a graph with countably many edges admits an injective edge
  colouring into ℕ, which has no monochromatic triangle (let alone K_{ℵ₀}).

Reference: https://www.erdosproblems.com/1174
Tags: set theory, ramsey theory

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §7.91. (Site-wide expansion of the key, recovered from the original
  pipeline's fetch of erdosproblems.com/latex/1172; the archived /latex/1174
  fetch contains no bibliographic entries. Stub — no fuller data available
  offline. Shelah's consistency result carries no citation key on the source
  page, so no reference is invented for it.)
-/

/--
Erdős Problem #1174, Part 1 [Va99, 7.91] (OPEN):

Does there exist a graph G with no K_4 (no 4-clique) such that for every
edge colouring of G with countably many colours (ℕ), some monochromatic K_3
(a 3-clique whose three edges all receive the same colour) exists in G?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC). The
source poses this as a yes/no question; this raw statement asserts the
affirmative direction, which is the only direction with known (consistency)
evidence.
-/
theorem erdos_problem_1174a :
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ S : Finset V, ¬G.IsNClique 4 S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Finset V) (c : ℕ), G.IsNClique 3 S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c :=
  sorry

/--
Erdős Problem #1174, Part 2 [Va99, 7.91] (OPEN):

Does there exist a graph G with no K_{ℵ_1} (no clique of cardinality ≥ ℵ_1)
such that for every edge colouring of G with countably many colours (ℕ), some
monochromatic K_{ℵ_0} exists — that is, a clique of cardinality ≥ ℵ_0 whose
edges all receive the same colour?

This is an open problem of Erdős and Hajnal. Shelah proved that such a graph
can consistently exist (i.e., its existence is consistent with ZFC). The
source poses this as a yes/no question; this raw statement asserts the
affirmative direction, which is the only direction with known (consistency)
evidence.
-/
theorem erdos_problem_1174b :
    ∃ (V : Type) (G : SimpleGraph V),
      (¬∃ S : Set V, aleph 1 ≤ Cardinal.mk ↥S ∧ G.IsClique S) ∧
      ∀ (col : V → V → ℕ), (∀ u v : V, col u v = col v u) →
        ∃ (S : Set V) (c : ℕ), aleph 0 ≤ Cardinal.mk ↥S ∧ G.IsClique S ∧
          ∀ u ∈ S, ∀ v ∈ S, u ≠ v → col u v = c :=
  sorry

end Erdos1174

end
