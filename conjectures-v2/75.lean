import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #75

*Reference:* [erdosproblems.com/75](https://www.erdosproblems.com/75)

Verbatim statement (recovered from the archived page, original pipeline fetch):

> Is there a graph of chromatic number ℵ₁ with ℵ₁ vertices such that for all ε > 0,
> if n is sufficiently large and H is a subgraph on n vertices, then H contains an
> independent set of size > n^{1-ε}? What about an independent set of size ≫ n?

Conjectured by Erdős, Hajnal, and Szemerédi [EHS82].

**Status: OPEN** (page banner; cross-checked against the teorth/erdosproblems metadata
mirror at commit a09c7a2, 2026-08-14: state "open", last update 2025-08-31).

Remarks from the page:
- In [Er95] Erdős asks this without the condition that the graph also have ℵ₁
  vertices, but this is an oversight, since already in [EHS82] they provide such a
  construction.
- In [Er95d] Erdős offers $1000 for a complete solution to all problems of this type
  (for example including also [74]), and a "generous reward for any significant
  partial results". (The mirror's per-problem prize field for #75 is "no": the $1000
  is for the collective class of problems, not this problem alone.)
- Related problems: [74], [750]. Tags: graph theory; chromatic number. No OEIS
  references.

Encoding notes:
- "Chromatic number ℵ₁" is encoded as `#V = aleph 1 ∧ ¬Nonempty (G.Coloring ℕ)`:
  no ℕ-coloring rules out every countable-or-finite coloring (compose with an
  embedding into ℕ), so χ(G) > ℵ₀; the identity coloring gives χ(G) ≤ #V = ℵ₁; and
  there is no cardinal strictly between ℵ₀ and ℵ₁, so χ(G) = ℵ₁ (in ZFC, no CH
  needed).
- "Every subgraph H on n vertices" is encoded as "every vertex subset S with
  |S| = n", with independence taken in G. The two readings are equivalent: any
  subgraph H with V(H) = S has E(H) ⊆ E(G[S]), so a G-independent T ⊆ V(H) is
  independent in H; conversely the induced subgraph G[S] realizes the hardest case.

Bibliography (from the archived `erdosproblems.com/latex/75` fetch — three
independent log captures, all agreeing):

[EHS82] Erdős, P., Hajnal, A., and Szemerédi, E., _On almost bipartite large
chromatic graphs_. Theory and practice of combinatorics (1982), 117-123.
(= Annals of Discrete Mathematics 12.)

[Er95] Erdős, Paul, _Some of my favourite problems in number theory, combinatorics,
and geometry_. Resenhas (1995), 165-186.

[Er95d] Erdős, Paul, _On some problems in combinatorial set theory_.
Publ. Inst. Math. (Beograd) (N.S.) (1995), 61-65.
-/

/--
Erdős Problem #75, Part 1 [EHS82,p.120][Er95,p.11][Er95d,p.63]:

There exists a graph G on ℵ₁ vertices with chromatic number ℵ₁ such that for
all ε > 0, if n is sufficiently large and S is any set of n vertices, then
S contains an independent set of size > n^{1-ε}.

This is the conjectured (affirmative) direction of the open question "Is there a
graph of chromatic number ℵ₁ with ℵ₁ vertices such that ... every subgraph on n
vertices contains an independent set of size > n^{1-ε}?"; quantifying over vertex
subsets S with independence in G is equivalent to quantifying over subgraphs H on
n vertices with independence in H (see the module docstring).
-/
theorem erdos_problem_75a :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      ¬Nonempty (G.Coloring ℕ) ∧
      ∀ ε : ℝ, ε > 0 →
        ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) > (n : ℝ) ^ ((1 : ℝ) - ε) :=
  sorry

/--
Erdős Problem #75, Part 2 [EHS82,p.120][Er95,p.11][Er95d,p.63]:

There exists a graph G on ℵ₁ vertices with chromatic number ℵ₁ such that
there exists c > 0 where every set of n ≥ 1 vertices contains an independent
set of size at least c · n.

This encodes the page's second question "What about an independent set of size
≫ n?" — i.e. independent sets of linear size. Requiring the bound for all n ≥ 1
rather than only for sufficiently large n is equivalent: given c that works for
n ≥ N, the constant min(c, 1/N) works for all n ≥ 1, since for 1 ≤ n < N a
singleton (independent, as simple graphs are loopless) already has size
1 ≥ n/N ≥ min(c, 1/N) · n. Likewise ≥ c·n and > c·n are interchangeable by
shrinking c. This linear property implies the property of Part 1 for the same
graph, since c·n > n^{1-ε} for n large.
-/
theorem erdos_problem_75b :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      #V = aleph 1 ∧
      ¬Nonempty (G.Coloring ℕ) ∧
      ∃ c : ℝ, c > 0 ∧
        ∀ n : ℕ, n ≥ 1 →
          ∀ S : Finset V, S.card = n →
            ∃ T : Finset V, T ⊆ S ∧
              (↑T : Set V).Pairwise (fun u v => ¬G.Adj u v) ∧
              (T.card : ℝ) ≥ c * (n : ℝ) :=
  sorry

end
