-- [AI - Claude Sonnet 5.5]: Erdős Problem 127 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Real Filter

/-!
# Erdős Problem #127: Bipartite Subgraphs Beyond the Edwards Bound

*Source:* [erdosproblems.com/127](https://www.erdosproblems.com/127) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20 as the tidied problem box). [Er97b]

Let $f(m)$ be maximal such that every graph with $m$ edges must contain a bipartite graph with
$$\geq \frac{m}{2}+\frac{\sqrt{8m+1}-1}{8}+f(m)$$
edges. Is there an infinite sequence of $m_i$ such that $f(m_i)\to \infty$?

Remarks recorded on the page:
* Conjectured by Erdős, Kohayakawa (the page spells it "Kohayakava"), and Gyárfás.
* Edwards [Ed73] proved that $f(m)\geq 0$ always. Note that $f(\binom{n}{2})= 0$, taking $K_n$.
* Solved by Alon [Al96], who showed $f(n^2/2)\gg n^{1/2}$, and also showed that
  $f(m)\ll m^{1/4}$ for all $m$. The best possible constant in $f(m)\leq Cm^{1/4}$ is unknown.

Tags: graph theory. OEIS: "Possible".

**Status.** The page banner reads PROVED. The mirror (`teorth/erdosproblems`) records `proved`
(2025-08-31) and `proved (Lean)` (2026-08-24), and upstream `erdos_127` is `answer(True)` with a
Lean proof link. The first pass asserts the asked ("yes") direction, which is the proved one.

**Real-valued $f$.** `f m` is the real infimum of the excess
$\mathrm{maxBip}(G)-\mathrm{edwardsLB}(m)$ over all graphs with $m$ edges. The maximal admissible
$f(m)$ is a real number, so that is the natural reading. Upstream takes the largest integer $k$,
which is the floor, and the two readings agree on whether $f(m_i)\to\infty$.

**The note $f(\binom n2)=0$.** The page's remark, and the first pass's docstring, hold exactly for
odd $n$. For $n=2k+1$, $\mathrm{edwardsLB}=k(k+1)=\lfloor n^2/4\rfloor$, so $K_n$ has excess $0$. For
even $n=2k$, $\mathrm{edwardsLB}=k^2-\tfrac14$ is not an integer, so every graph with $\binom n2$
edges has a bipartite subgraph with at least $k^2$ edges, an excess of at least $\tfrac14$. $K_n$
attains $k^2$, so $f(\binom{2k}{2})=\tfrac14$. For example $f(1)=f(6)=\tfrac14$. The integer-valued
reading gives $0$ in both cases. See `variants.complete_odd` and `variants.complete_even`.

**Encoding.**
* `cutSize G S` counts the edges with exactly one endpoint in `S`, once each, as ordered pairs
  from the $S$ side.
* `maxBipartiteSubgraphSize G` is the maximum cut. It equals the largest number of edges of a
  bipartite subgraph: such a subgraph's edges lie in the cut of its bipartition.
* The set defining `f m` is nonempty (a path on $m+1$ vertices has $m$ edges) and bounded below
  (cut sizes are nonnegative, so by $-\mathrm{edwardsLB}(m)$), so `sInf` is the true infimum, with
  no junk value. Cut sizes are integers in $[0,m]$, so the infimum is attained.
* The graphs range over finite vertex types in `Type`. Every finite graph is isomorphic to one.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [Ed73] Edwards, C. S., _Some extremal properties of bipartite subgraphs_. Canad. J. Math.
  (1973), 475–485.
* [Al96] Alon, N., _Bipartite subgraphs_. Combinatorica (1996), 301–311.

(Provenance: no `/latex/127` fetch exists in the session logs, and the one WebFetch of the page
carries no bibliography. All three entries are from upstream `127.lean`.)
-/

/--
For a finite simple graph G and a vertex subset S, the cut defined by S
consists of edges with exactly one endpoint in S. The cut is counted as ordered pairs
(v, w) with v ∈ S, w ∉ S, and G.Adj v w; since G.Adj is symmetric and S and Sᶜ
are disjoint, each undirected cut edge is counted exactly once (from its S-side endpoint).
-/
noncomputable def cutSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V =>
    p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2).card

/--
The maximum bipartite subgraph size of G: the maximum over all vertex bipartitions
(S, Sᶜ) of the number of edges crossing the cut. This equals the maximum number of
edges in any bipartite subgraph of G (the max-cut).
-/
noncomputable def maxBipartiteSubgraphSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (cutSize G)

/--
The Edwards lower bound: every graph with m edges has a bipartite subgraph of size at
least m/2 + (√(8m+1) − 1)/8. Proved by Edwards [Ed73].
-/
noncomputable def edwardsLB (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/--
f(m) is the maximal value r such that every finite simple graph with m edges has a
bipartite subgraph with at least edwardsLB(m) + r edges. Equivalently, f(m) is the
infimum over all finite simple graphs G with exactly m edges of the excess
  maxBipartiteSubgraphSize(G) − edwardsLB(m).

Edwards [Ed73] proved f(m) ≥ 0 for all m. Note that f(C(n,2)) = 0 for odd n, achieved by Kₙ.
For even n, Kₙ has excess 1/4, and so does every graph with C(n,2) edges, so f(C(n,2)) = 1/4.
-/
noncomputable def f (m : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = m ∧ r = (maxBipartiteSubgraphSize G : ℝ) - edwardsLB m}

/--
Erdős Problem #127 [Er97b] (Erdős–Kohayakawa–Gyárfás; PROVED by Alon [Al96]):
Let f(m) be maximal such that every graph with m edges contains a bipartite subgraph with
at least m/2 + (√(8m+1) − 1)/8 + f(m) edges.
There exists an infinite sequence of integers (mᵢ) with mᵢ → ∞ such that f(mᵢ) → ∞.

Edwards [Ed73] proved f(m) ≥ 0 for all m.
Alon [Al96] proved this in the affirmative: f(n²/2) ≫ n^(1/2).
Alon [Al96] also showed the upper bound f(m) ≪ m^(1/4) for all m.
-/
theorem erdos_problem_127 :
    ∃ (seq : ℕ → ℕ), StrictMono seq ∧
      Filter.Tendsto (fun i => f (seq i)) Filter.atTop Filter.atTop :=
  sorry

/--
Edwards [Ed73] (PROVED): f(m) ≥ 0 for every m.
-/
theorem erdos_problem_127.variants.edwards : ∀ m : ℕ, 0 ≤ f m :=
  sorry

/--
Alon's lower bound [Al96] (PROVED): f(n²/2) ≫ n^{1/2}. Here n is even, so that n²/2 is an integer.
-/
theorem erdos_problem_127.variants.alon_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, Even n → c * Real.sqrt n ≤ f (n ^ 2 / 2) :=
  sorry

/--
Alon's upper bound [Al96] (PROVED): f(m) ≪ m^{1/4} for all m. The best constant is unknown.
-/
theorem erdos_problem_127.variants.alon_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, f m ≤ C * (m : ℝ) ^ (1 / 4 : ℝ) :=
  sorry

/--
The page's note for odd n (PROVED): f(C(n, 2)) = 0 for n = 2k + 1. Here C(2k+1, 2) = (2k+1)k, and
K_{2k+1} attains the Edwards bound exactly.
-/
theorem erdos_problem_127.variants.complete_odd :
    ∀ k : ℕ, f ((2 * k + 1) * k) = 0 :=
  sorry

/--
The same note for even n is not exact (PROVED): f(C(n, 2)) = 1/4 for n = 2k, k ≥ 1. Here
C(2k, 2) = k(2k-1). The Edwards bound is k² - 1/4, so every such graph has a bipartite subgraph
with at least k² edges, and K_{2k} attains k².
-/
theorem erdos_problem_127.variants.complete_even :
    ∀ k : ℕ, 1 ≤ k → f (k * (2 * k - 1)) = 1 / 4 :=
  sorry
