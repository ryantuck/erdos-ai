-- [AI - Claude Opus 5.5]: Erdős Problem 108 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph Filter

/-!
# Erdős Problem #108

*Source:* [erdosproblems.com/108](https://www.erdosproblems.com/108) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; page last edited 23 January
2026, captured 2026-02-19 and 2026-03-05). [Er71] [Er79b] [Er81] [Er90] [Er95d] [Va99, 3.59]

For every r ≥ 4 and k ≥ 2 is there some finite f(k,r) such that every graph
of chromatic number ≥ f(k,r) contains a subgraph of girth ≥ r and chromatic
number ≥ k?

Remarks recorded on the page:
* Conjectured by Erdős and Hajnal. Rödl [Ro77] proved the r = 4 case (see #923).
* The infinite version is also open: does every graph of infinite chromatic number contain a
  subgraph of infinite chromatic number whose girth is > k? See #740 for the infinitary
  version.
* In [Er79b] Erdős also asks whether $\lim_{k\to\infty} f(k,r+1)/f(k,r) = \infty$.
* See also the entry in the graphs problem collection.

**Encoding.** Graphs are finite (`Fintype V`). This loses nothing for the finite-χ question:
by the de Bruijn–Erdős compactness theorem, a graph with χ ≥ f has a finite subgraph with
χ ≥ f, so the statement for finite graphs implies it for all graphs. Girth and chromatic number
are Mathlib's `ℕ∞`-valued `girth` and `chromaticNumber`. A forest has girth `⊤`, which counts
as large girth.

Tags: graph theory, chromatic number, cycles. OEIS: "possible".

## References

* [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.
* [Er79b] Erdős, P. (1979). Stub: not recovered.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er95d] Erdős, P., _On some problems in combinatorial set theory_. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61–65.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999.
* [Ro77] Rödl, V., _On the chromatic number of subgraphs of a given graph_. Proc. Amer. Math.
  Soc. (1977), 370–371.

(Provenance: the original pipeline's `/latex` extractions for sibling problems. [Er71] comes
from `/latex/1006`, `/latex/1008`, `/latex/1016` and others, which agree. [Ro77] and
[Er95d] come from single extractions and agree with upstream formal-conjectures entries.
[Er79b] is not in any extraction.)
-/

/--
**Erdős Problem #108** [Er71, Er79b, Er81, Er90, Er95d] (OPEN):

For every r ≥ 4 and k ≥ 2 there exists a finite f(k,r) such that every graph
of chromatic number ≥ f(k,r) contains a subgraph of girth ≥ r and chromatic
number ≥ k.
-/
theorem erdos_problem_108 (r : ℕ) (hr : r ≥ 4) (k : ℕ) (hk : k ≥ 2) :
    ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      f ≤ G.chromaticNumber →
      ∃ (G' : G.Subgraph),
        r ≤ G'.coe.girth ∧ k ≤ G'.coe.chromaticNumber :=
  sorry

/--
Rödl [Ro77] (PROVED): the case r = 4. Graphs of large enough chromatic number contain
triangle-free subgraphs (girth ≥ 4) of chromatic number ≥ k.
-/
theorem erdos_problem_108.variants.rodl (k : ℕ) (hk : k ≥ 2) :
    ∃ f : ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      f ≤ G.chromaticNumber →
      ∃ (G' : G.Subgraph), 4 ≤ G'.coe.girth ∧ k ≤ G'.coe.chromaticNumber :=
  sorry

/--
The infinite version (OPEN; compare #740): every graph of infinite chromatic number contains,
for each `k`, a subgraph of infinite chromatic number and girth greater than `k`.
-/
theorem erdos_problem_108.variants.infinite (k : ℕ) :
    ∀ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ →
      ∃ (G' : G.Subgraph), (k : ℕ∞) < G'.coe.girth ∧ G'.coe.chromaticNumber = ⊤ :=
  sorry

/--
The least admissible `f(k, r)`: the least `f` such that every finite graph with χ ≥ `f` has a
subgraph of girth ≥ `r` and χ ≥ `k`. If no such `f` exists, i.e. the conjecture fails at
`(k, r)`, `sInf ∅ = 0` is a junk value.
-/
noncomputable def fMin (k r : ℕ) : ℕ :=
  sInf {f : ℕ | ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    f ≤ G.chromaticNumber →
      ∃ (G' : G.Subgraph), r ≤ G'.coe.girth ∧ k ≤ G'.coe.chromaticNumber}

/--
Erdős's question from [Er79b] (OPEN): is $f(k, r+1)/f(k, r) \to \infty$ as $k \to \infty$?
It is written without division: for every `C`, eventually `C · f(k, r) ≤ f(k, r+1)`. This is
meaningful under `erdos_problem_108`, which makes `fMin` finite and at least `k`.
-/
theorem erdos_problem_108.variants.ratio (r : ℕ) (hr : r ≥ 4) :
    ∀ C : ℝ, ∀ᶠ k : ℕ in atTop, C * (fMin k r : ℝ) ≤ (fMin k (r + 1) : ℝ) :=
  sorry
