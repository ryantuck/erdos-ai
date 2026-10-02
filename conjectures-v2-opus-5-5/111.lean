-- [AI - Claude Opus 5.5]: Erdős Problem 111 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open SimpleGraph Cardinal

/-!
# Erdős Problem #111

*Source:* [erdosproblems.com/111](https://www.erdosproblems.com/111) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the
tidied problem box). [Er81] [EHS82] [Er87] [Er90] [Er97d] [Er97f]

If $G$ is a graph let $h_G(n)$ be defined such that any subgraph of $G$ on $n$ vertices can be
made bipartite after deleting at most $h_G(n)$ edges. What is the behaviour of $h_G(n)$? Is it
true that $h_G(n)/n \to \infty$ for every graph $G$ with chromatic number $\aleph_1$?

Remarks recorded on the page:
* A problem of Erdős, Hajnal and Szemerédi [EHS82]. Every $G$ with chromatic number $\aleph_1$
  must have $h_G(n) \gg n$, since $G$ must contain, for some $r$, $\aleph_1$ many
  vertex-disjoint odd cycles of length $2r+1$.
* Erdős, Hajnal and Szemerédi proved that there is a $G$ with chromatic number $\aleph_1$
  such that $h_G(n) \ll n^{3/2}$. In [Er81] Erdős conjectured that this can be improved to
  $\ll n^{1+\varepsilon}$ for every $\varepsilon > 0$.
* See also Problem #74.

**Encoding.** `hFun G n` maximises over *induced* $n$-vertex subgraphs. That equals the
maximum over all $n$-vertex subgraphs, because deleting edges never makes a graph harder to
make bipartite. The page's explicit question is `erdos_problem_111`. The first pass had
formalized only the [Er81] remark, as its main theorem; that statement is kept below as
`erdos_problem_111.variants.er81`.

Tags: graph theory, chromatic number, set theory.

## References

* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [EHS82] Erdős, P., Hajnal, A. and Szemerédi, E., _On almost bipartite large chromatic
  graphs_. Theory and Practice of Combinatorics (1982), 117–123.
* [Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and combinatorics
  (Arcata, Calif., 1985) (1987), 223–228.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er97d] Erdős, P., _Some recent problems and results in graph theory_. Discrete Math.
  (1997), 81–85.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/111` for [Er81] and
[EHS82]. Sibling `/latex` extractions for the others.)
-/

/--
A graph G (on vertex type V) has chromatic number ℵ₁ if it cannot be properly
colored with countably many colors but can be properly colored with ℵ₁ colors.
-/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/--
The minimum number of edges that must be deleted from a finite graph H to make
it bipartite (i.e., properly 2-colorable).
-/
noncomputable def minEdgeDeletionsForBipartite {W : Type*} [Fintype W]
    (H : SimpleGraph W) : ℕ :=
  sInf {k : ℕ | ∃ H' : SimpleGraph W,
    H' ≤ H ∧
    Nonempty (H'.Coloring (Fin 2)) ∧
    (H.edgeSet \ H'.edgeSet).ncard = k}

/--
For a graph G and n : ℕ, hFun G n is defined as the maximum over all n-vertex
induced subgraphs H of G of the minimum number of edges that must be deleted
from H to make it bipartite.

That is, hFun G n is the smallest k such that every induced subgraph of G on
exactly n vertices can be made bipartite by deleting at most k edges.
-/
noncomputable def hFun {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (S : Finset V),
    S.card = n ∧
    k = minEdgeDeletionsForBipartite (G.induce (S : Set V))}

/--
Erdős Problem #111 (OPEN), the page's question: is $h_G(n)/n \to \infty$ for every graph $G$
with chromatic number $\aleph_1$? The asked direction is asserted: for every such $G$ and
every $C$, eventually $h_G(n) \ge C n$.
-/
theorem erdos_problem_111 :
    ∀ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAleph1 G →
      ∀ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ≤ (hFun G n : ℝ) :=
  sorry

/--
Erdős's conjecture from [Er81] (OPEN; this was the first-pass main theorem, kept byte for
byte): some graph $G$ with chromatic number $\aleph_1$ has $h_G(n) \ll n^{1+\varepsilon}$ for
every $\varepsilon > 0$.

Background:
- For every G with chromatic number ℵ₁, hFun G n ≫ n, since G must contain ℵ₁
  many vertex-disjoint odd cycles of some fixed length 2r+1.
- Erdős–Hajnal–Szemerédi [EHS82] proved there exists G with chromatic number ℵ₁
  satisfying hFun G n ≪ n^{3/2}.
-/
theorem erdos_problem_111.variants.er81 :
    ∃ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAleph1 G ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ n : ℕ, (hFun G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) :=
  sorry

/--
[EHS82] (PROVED): every $G$ with chromatic number $\aleph_1$ has $h_G(n) \gg n$. It contains
$\aleph_1$ vertex-disjoint odd cycles of some length $2r+1$, and each needs its own deleted
edge.
-/
theorem erdos_problem_111.variants.linear_lower :
    ∀ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAleph1 G →
      ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) ≤ (hFun G n : ℝ) :=
  sorry

/--
Erdős, Hajnal and Szemerédi [EHS82] (PROVED): some $G$ with chromatic number $\aleph_1$ has
$h_G(n) \ll n^{3/2}$.
-/
theorem erdos_problem_111.variants.ehs_three_halves :
    ∃ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAleph1 G ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (hFun G n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry
