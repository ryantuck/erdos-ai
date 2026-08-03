/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1032

*Reference:* [erdosproblems.com/1032](https://www.erdosproblems.com/1032)

Erdős asked whether there exists a constant $c > 0$ such that for arbitrarily large $n$,
there is a $4$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$.
In [Er93] Erdős said he asked this "more than 20 years ago". The problem is **open**
(erdosproblems.com page edition of 23 January 2026).

Toft conjectured that a $4$-chromatic critical graph on $n$ vertices has at least
$(\frac{5}{3} + o(1))n$ edges, and has examples to show this would be best possible.
(The source page prints "vertices" in place of "edges", which is literally false — a
graph on $n$ vertices has exactly $n$ vertices — so the intended edge-count reading is
recorded here.) This conjecture is not formalized below: the edge-critical predicate
`IsCritical` used in this file tolerates isolated vertices (e.g. $K_4$ together with
$n - 4$ isolated vertices satisfies `IsCritical G 4` with only $6$ edges), so a faithful
formalization would additionally need a no-isolated-vertices hypothesis. The min-degree
statements below are unaffected, since a positive minimum-degree bound already excludes
isolated vertices.

- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Mathematicae **16** (1993), 333–350.
- [Si72] Simonovits, M., _On colour-critical graphs_. Studia Scientiarum Mathematicarum
  Hungarica (1972), 67–81.
- [To72] Toft, B., _Two theorems on critical 4-chromatic graphs_. Studia Scientiarum
  Mathematicarum Hungarica (1972), 83–89.
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.60.

See also problems 917 and 944.
-/

open SimpleGraph

namespace Erdos1032

/--
A simple graph $G$ is $k$-critical if its chromatic number equals $k$ and for every
edge $e$, the graph obtained by deleting $e$ has chromatic number strictly less
than $k$.
-/
def IsCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧ ∀ e ∈ G.edgeSet, G.IsCriticalEdge e

/--
**Erdős Problem 1032** [Er93, p.341]:

Is there a constant $c > 0$ such that for arbitrarily large $n$, there exists
a $4$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$?

Known results:
- Simonovits [Si72] and Toft [To72] independently constructed $4$-chromatic
  critical graphs with minimum degree $\gg n^{1/3}$.
- Dirac gave an example of a $6$-chromatic critical graph with minimum degree $> n/2$.
- This problem is also open for $5$-chromatic critical graphs.
-/
@[category research open, AMS 5]
theorem erdos_1032 : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 4 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) := by
  sorry

/--
**Erdős Problem 1032 (5-chromatic variant)**:

Is there a constant $c > 0$ such that for arbitrarily large $n$, there exists
a $5$-chromatic critical graph on $n$ vertices with minimum degree at least $c \cdot n$?

This variant is also mentioned as open in [Er93, p.341].
-/
@[category research open, AMS 5]
theorem erdos_1032.variants.five_chromatic : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 5 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) := by
  sorry

/--
**Erdős Problem 1032 (Simonovits–Toft partial result)** [Si72] [To72]:

Simonovits and Toft independently constructed $4$-chromatic critical graphs with
minimum degree $\gg n^{1/3}$: there is a constant $c > 0$ such that for arbitrarily
large $n$ there exists a $4$-chromatic critical graph on $n$ vertices with minimum
degree at least $c \cdot n^{1/3}$.
-/
@[category research solved, AMS 5]
theorem erdos_1032.variants.simonovits_toft :
    ∃ c : ℝ, c > 0 ∧ ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 4 ∧ (G.minDegree : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

/--
**Erdős Problem 1032 (Dirac's $6$-chromatic example)**:

Dirac gave an example of a $6$-chromatic critical graph with minimum degree $> n/2$:
for arbitrarily large $n$ there exists a $6$-chromatic critical graph on $n$ vertices
with minimum degree greater than $n/2$. (Dirac's construction joins two disjoint odd
cycles $C_{2m+1}$ completely, giving such graphs on $n = 4m + 2$ vertices with minimum
degree $2m + 3 > n/2$.)
-/
@[category research solved, AMS 5]
theorem erdos_1032.variants.dirac_six_chromatic :
    ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        IsCritical G 6 ∧ (G.minDegree : ℝ) > (n : ℝ) / 2 := by
  sorry

end Erdos1032
