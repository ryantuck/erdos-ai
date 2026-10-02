-- [AI - Claude Opus 5.5]: Erdős Problem 113 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-!
# Erdős Problem #113: Turán Numbers of Bipartite Graphs and 2-Degeneracy

*Source:* [erdosproblems.com/113](https://www.erdosproblems.com/113) (status **DISPROVED**:
"This has been solved in the negative."; prize \$500; captured 2026-02-19 as the tidied problem
box). [ErSi84] [Er90] [Er91] [Er93]

If $G$ is bipartite then $\mathrm{ex}(n;G)\ll n^{3/2}$ if and only $G$ is $2$-degenerate, that
is, $G$ contains no induced subgraph with minimal degree at least 3.

Remarks recorded on the page:
* Conjectured by Erdős and Simonovits [ErSi84]. Erdős first offered \$250 for a proof and \$100
  for a counterexample, but in [Er93] offered \$500 for a counterexample.
* Disproved by Janzer [Ja23b] who constructed, for any $\epsilon>0$, a $3$-regular bipartite
  graph $H$ such that $\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}$.
* See also Problems #146 and #147 and the entry in the graphs problem collection.

**Polarity.** The conjecture is false, so `erdos_problem_113` asserts its negation. The inner
proposition is the first pass's, byte for byte. The first pass asserted the conjecture itself,
while its docstring said it was disproved.

**Both directions fail.** Janzer's graph refutes the "only if" direction: a Turán number
$\ll n^{3/2}$ does not force 2-degeneracy. The "if" direction is the case $r = 2$ of Problem
#146, which was open when this page was captured. The mirror now records #146 as disproved, by
a machine-checked counterexample in [OpenAI26]: a bipartite 2-degenerate $H$ with
$\mathrm{ex}(n;H) \ge c\,n^{3/2+\varepsilon}$ for all large $n$. The sources are mirror
commits `be86208` (2026-08-02) and `7b7132c` (2026-08-31), and upstream
`erdos_146.variants.two_degenerate_counterexample`. This second-pass review has not checked
that counterexample.

Tags: graph theory, turan number.

## References

* [ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_.
  Progress in graph theory (Waterloo, Ont., 1982) (1984), 203–218.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number
  theory_. Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991),
  397–406.
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350.
* [Ja23b] Janzer, O., _Disproof of a conjecture of Erdős and Simonovits on the Turán number of
  graphs with minimum degree 3_. Int. Math. Res. Not. IMRN (2023), 8478–8494.
* [OpenAI26] OpenAI, _Ten advances in mathematics and theoretical computer science_ (2026).
  Not cited on the captured page; the entry is from upstream `146.lean`.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/113` for [ErSi84],
[Er93] and [Ja23b]. Sibling `/latex` extractions for [Er90] and [Er91], which agree with
upstream `113.lean`.)
-/

/-- An injective graph homomorphism from H to F; witnesses that F contains a
    subgraph isomorphic to H. -/
def containsSubgraph {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph F H ∧ F.edgeFinset.card = m}

/-- A graph G is 2-degenerate if every non-empty finite set of vertices contains
    a vertex with at most 2 neighbors within that set.  Equivalently, G has no
    induced subgraph with minimum degree at least 3. -/
def IsTwoDegenerateGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ 2

/--
Erdős Problem #113 [ErSi84] (DISPROVED by Janzer [Ja23b]). The Erdős–Simonovits conjecture is
false: it is not the case that every finite bipartite graph G has ex(n; G) ≪ n^{3/2} exactly
when G is 2-degenerate.

Here ex(n; G) ≪ n^{3/2} means there is a constant C > 0 with ex(n; G) ≤ C · n^{3/2} for all n.
Both sides vanish at n = 0, so "for all n" is no stronger than "for all large n".

Janzer [Ja23b]: for any ε > 0 there is a 3-regular bipartite graph H with
ex(n; H) ≪ n^{4/3 + ε}. A 3-regular graph is not 2-degenerate. Taking ε ≤ 1/6, its Turán number
is ≪ n^{3/2}, so the "only if" direction (ex(n; G) ≪ n^{3/2} → G is 2-degenerate) fails.
-/
theorem erdos_problem_113 :
    ¬ (∀ (U : Type*) (G : SimpleGraph U) [Fintype U] [DecidableRel G.Adj],
      Nonempty (G.Coloring (Fin 2)) →
      (IsTwoDegenerateGraph G ↔
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          (turanNumber G n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ))) :=
  sorry

/--
Janzer [Ja23b] (PROVED): for every ε > 0 there is a nonempty, finite, 3-regular bipartite graph
H with ex(n; H) ≪ n^{4/3 + ε}. `Nonempty U` excludes the graph on no vertices, which is
vacuously 3-regular.
-/
theorem erdos_problem_113.variants.janzer :
    ∀ ε : ℝ, 0 < ε →
      ∃ (U : Type) (_ : Fintype U) (_ : Nonempty U) (H : SimpleGraph U),
        (∀ u : U, (H.neighborSet u).ncard = 3) ∧
        Nonempty (H.Coloring (Fin 2)) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 + ε) :=
  sorry

/--
The "only if" direction fails (PROVED; [Ja23b] with ε = 1/6): some finite bipartite graph that
is not 2-degenerate has ex(n; H) ≪ n^{3/2}.
-/
theorem erdos_problem_113.variants.only_if_fails :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U),
      Nonempty (H.Coloring (Fin 2)) ∧ ¬ IsTwoDegenerateGraph H ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) :=
  sorry

/--
The "if" direction fails too (DISPROVED; the case r = 2 of Problem #146): a machine-checked
counterexample [OpenAI26] gives a finite bipartite 2-degenerate graph H whose Turán number is not
≪ n^{3/2}. The status comes from the mirror (commits `be86208`, `7b7132c`) and upstream
`erdos_146.variants.two_degenerate_counterexample`. This review has not checked the
counterexample.
-/
theorem erdos_problem_113.variants.if_fails :
    ∃ (U : Type) (_ : Fintype U) (H : SimpleGraph U),
      Nonempty (H.Coloring (Fin 2)) ∧ IsTwoDegenerateGraph H ∧
      ¬ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
        (turanNumber H n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ) :=
  sorry
