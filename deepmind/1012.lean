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
# Erdős Problem 1012

*Reference:* [erdosproblems.com/1012](https://www.erdosproblems.com/1012)

Let $k \geq 0$. Let $f(k)$ be the least integer such that every graph on $n \geq f(k)$
vertices with at least $\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle
of length $n-k$. Determine or estimate $f(k)$.

Erdős [Er62e] proved that $f(k)$ exists for all $k \geq 0$ (see also [Er71, p.98]);
this is not immediately stated in [Er62e], but Cambie has explained (in the comments on
the problem page) why the existence of $f(k)$ follows from the result of [Er62e].
Ore [Or61] proved $f(0) = 1$ (every graph on $n \geq 1$ vertices with at least
$\binom{n-1}{2} + 2$ edges contains a Hamiltonian cycle).
Bondy [Bo71b] proved $f(1) = 1$.

Woodall [Wo72] proved that every graph on $n \geq 2k+3$ vertices with at least
$\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle of length $\ell$ for all
$3 \leq \ell \leq n-k$. This settles the question completely; in particular
$f(k) \leq 2k + 3$. (Note that $2k + 3$ is not the exact value of $f(k)$ in general:
by the results of Ore and Bondy above, $f(0) = f(1) = 1$.)

The problem is listed as SOLVED on erdosproblems.com (page last edited 28 December 2025,
accessed 2026-02-22).

[Er62e] Erdős, P., _Remarks on a paper of Pósa_. Magyar Tudományos Akadémia Matematikai
Kutató Intézet Közleményei (1962), 227–229.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proceedings of Conference, Oxford, 1969)
(1971), 97–109.

[Or61] Ore, O., _Arc coverings of graphs_. Annali di Matematica Pura ed Applicata, 4th
series (1961), 315–321.

[Bo71b] Bondy, J. A., _Large cycles in graphs_. Discrete Mathematics (1971/72), 121–132.

[Wo72] Woodall, D. R., _Sufficient conditions for circuits in graphs_. Proceedings of the
London Mathematical Society, 3rd series (1972), 739–755.
-/

open SimpleGraph

namespace Erdos1012

/--
Erdős Problem 1012 [Er62e] (solved by Woodall [Wo72]):

For every $k \geq 0$ and $n \geq 2k + 3$, every simple graph on $n$ vertices with at least
$\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle of length $\ell$ for every
$3 \leq \ell \leq n - k$.

In particular, taking $\ell = n - k$, every $n \geq 2k + 3$ satisfies the defining
property of $f(k)$, so $f(k) \leq 2k + 3$, answering Erdős' original question.
-/
@[category research solved, AMS 5]
theorem erdos_1012 (k n : ℕ) (hn : n ≥ 2 * k + 3)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1)
    (l : ℕ) (hl₁ : 3 ≤ l) (hl₂ : l ≤ n - k) :
    ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = l := by
  sorry

/--
Erdős [Er62e] proved that $f(k)$ exists for all $k \geq 0$: for every $k$ there is a
threshold $N$ such that every graph on $n \geq N$ vertices with at least
$\binom{n-k-1}{2} + \binom{k+2}{2} + 1$ edges contains a cycle of length $n - k$.
(By Woodall's theorem [Wo72], $N = 2k + 3$ suffices.)
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.exists_threshold (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      G.edgeFinset.card ≥ Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1 →
      ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = n - k := by
  sorry

/--
Ore [Or61] proved $f(0) = 1$: every graph on $n \geq 1$ vertices with at least
$\binom{n-1}{2} + 2$ edges contains a Hamiltonian cycle (a cycle of length $n$).

For $n \leq 2$ the edge hypothesis is unsatisfiable (such a graph has at most one edge,
while the threshold is at least $2$), so the statement holds vacuously there, matching
the informal claim.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.ore (n : ℕ) (hn : n ≥ 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ Nat.choose (n - 1) 2 + 2) :
    ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  sorry

/--
Bondy [Bo71b] proved $f(1) = 1$: every graph on $n \geq 1$ vertices with at least
$\binom{n-2}{2} + \binom{3}{2} + 1$ edges contains a cycle of length $n - 1$.

For $n \leq 3$ the edge hypothesis is unsatisfiable (such a graph has at most three
edges, while the threshold is at least $4$), so the statement holds vacuously there; in
particular the ℕ-truncated values of $n - 2$ and $n - 1$ at small $n$ are harmless.
-/
@[category research solved, AMS 5]
theorem erdos_1012.variants.bondy (n : ℕ) (hn : n ≥ 1)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ Nat.choose (n - 2) 2 + Nat.choose 3 2 + 1) :
    ∃ (v : Fin n) (p : G.Walk v v), p.IsCycle ∧ p.length = n - 1 := by
  sorry

end Erdos1012
