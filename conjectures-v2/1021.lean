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

import FormalConjecturesUtil

/-!
# Erdős Problem 1021

*Reference:* [erdosproblems.com/1021](https://www.erdosproblems.com/1021)

Is it true that, for every $k \ge 3$, there is a constant $c_k > 0$ such that
$$\mathrm{ex}(n, G_k) \ll n^{3/2 - c_k},$$
where $G_k$ is the 1-subdivision of $K_k$: the bipartite graph between
$\{y_1, \ldots, y_k\}$ and $\{z_1, \ldots, z_{\binom{k}{2}}\}$, with each $z_j$ joined to a
unique pair of $y_i$?

A conjecture of Erdős and Simonovits [Er71, p.103][Er74c, p.79], who also proved
(in unpublished work) that in any such result one must have $c_k \to 0$ as
$k \to \infty$. Erdős [Er71] could not even prove whether
$\mathrm{ex}(n, G_k) = o(n^{3/2})$. The graph $G_k$ is the graph $H_k$ of
Erdős Problem 926 with the vertex $x$ omitted.

The conjecture was proved by Conlon and Lee [CoLe21] with $c_k = 6^{-k}$, later
improved to $c_k = 1/(4k-6)$ by Janzer [Ja19]. The problem page is marked
PROVED ("solved in the affirmative").

When $k = 3$ the graph $G_3$ is the six-cycle $C_6$, for which Erdős [Er64c] and
Bondy–Simonovits [BoSi74] proved $\mathrm{ex}(n, C_6) \ll n^{4/3}$ (cf. Erdős
Problem 572). Note: the problem page states this bound as $n^{7/6}$, which
appears to be an error — $C_6$-free graphs with $\gg n^{4/3}$ edges exist
(incidence graphs of generalized quadrangles, girth $8$), and the
Bondy–Simonovits even-cycle theorem $\mathrm{ex}(n, C_{2\ell}) \ll \ell \cdot
n^{1+1/\ell}$ gives exactly $n^{4/3}$ at $2\ell = 6$.

[Er64c] Erdős, P., _Extremal problems in graph theory_.
Theory of Graphs and its Applications (Proc. Sympos. Smolenice, 1963) (1964), 29–36.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proceedings of Conference, Oxford, 1969)
(1971), 97–109.

[Er74c] Erdős, P., _Extremal problems on graphs and hypergraphs_. (1974), 75–84.
(Bibliographic stub: this key is cited by the problem page but absent from its
LaTeX bibliography; title and pages as used for this key by the sibling
formalizations of Erdős Problems 926, 576, 1075 and 1076.)

[BoSi74] Bondy, J.A. and Simonovits, M., _Cycles of even length in graphs_.
J. Combin. Theory Ser. B 16 (1974), 97–105.

[CoLe21] Conlon, D. and Lee, J., _On the extremal number of subdivisions_.
Int. Math. Res. Not. IMRN (2021), 9122–9145.

[Ja19] Janzer, O., _Improved bounds for the extremal number of subdivisions_.
Electron. J. Combin. 26 (2019), Paper No. 3.3, 6 pp.
-/

open SimpleGraph

namespace Erdos1021

/-- Adjacency in the 1-subdivision of $K_k$. Vertices are "original" (`Fin k`) or
"edge" (`{(i, j) : i < j}`). Each edge-vertex is adjacent to exactly its two
original endpoints. -/
def subdivKAdj (k : ℕ) :
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} →
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} → Prop
  | .inl a, .inr ⟨⟨i, j⟩, _⟩ => a = i ∨ a = j
  | .inr ⟨⟨i, j⟩, _⟩, .inl a => a = i ∨ a = j
  | _, _ => False

/-- The 1-subdivision of $K_k$. The vertex set is the disjoint union of the
$k$ original vertices and the $\binom{k}{2}$ edge-subdivision vertices.
Each edge-vertex is adjacent to exactly the two endpoints of its
corresponding edge in $K_k$. -/
def subdivisionKComplete (k : ℕ) :
    SimpleGraph (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}) where
  Adj := subdivKAdj k
  symm := by
    intro v w h
    rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> rcases w with b | ⟨⟨i', j'⟩, hij'⟩ <;> exact h
  loopless := fun v h => by rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> exact h

/-- A graph $G$ contains $H$ as a subgraph if there is an injective vertex map
that sends edges to edges. -/
def containsSubgraph {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem 1021 [Er71, p.103][Er74c, p.79]:

For every $k \ge 3$, there exists $c_k > 0$ and $C > 0$ such that every $n$-vertex
graph not containing the 1-subdivision of $K_k$ as a subgraph has at most
$C \cdot n^{3/2 - c_k}$ edges.

Proved by Conlon and Lee [CoLe21] with $c_k = 6^{-k}$. Improved to
$c_k = 1/(4k-6)$ by Janzer [Ja19].
-/
@[category research solved, AMS 5]
theorem erdos_1021 : answer(True) ↔
    ∀ (k : ℕ), k ≥ 3 →
    ∃ (c : ℝ), c > 0 ∧ ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete k) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - c) := by sorry

/--
The special case $k = 3$ of Erdős Problem 1021: the 1-subdivision of $K_3$ is
the 6-cycle $C_6$. Erdős [Er64c] and Bondy–Simonovits [BoSi74] proved that
$\mathrm{ex}(n, C_6) \le C \cdot n^{1 + 1/3}$, giving $c_3 = 1/6$ (since
$3/2 - 1/6 = 4/3 = 1 + 1/3$). This exponent is optimal, coincides with Janzer's
general $c_k = 1/(4k-6)$ at $k = 3$, and is much stronger than the
$c_k = 6^{-k}$ of Conlon–Lee. (The problem page states the bound as $n^{7/6}$;
this appears to be an error — see the module docstring.)
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.C6 :
    ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete 3) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3) := by sorry

/--
The explicit form proved by Conlon and Lee [CoLe21]: for every $k \ge 3$ the
constant $c_k = 6^{-k}$ is admissible, i.e.
$\mathrm{ex}(n, G_k) \ll n^{3/2 - 6^{-k}}$.
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.conlon_lee :
    ∀ (k : ℕ), k ≥ 3 →
    ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete k) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - ((6 : ℝ) ^ k)⁻¹) := by
  sorry

/--
The improved explicit form proved by Janzer [Ja19]: for every $k \ge 3$ the
constant $c_k = 1/(4k-6)$ is admissible, i.e.
$\mathrm{ex}(n, G_k) \ll n^{3/2 - 1/(4k-6)}$.
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.janzer :
    ∀ (k : ℕ), k ≥ 3 →
    ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete k) →
    (G.edgeFinset.card : ℝ) ≤
      C * (n : ℝ) ^ ((3 : ℝ) / 2 - 1 / (4 * (k : ℝ) - 6)) := by
  sorry

/--
Erdős and Simonovits proved (in unpublished work, per the problem page) that in
any result of the form $\mathrm{ex}(n, G_k) \ll n^{3/2 - c_k}$ one must have
$c_k \to 0$ as $k \to \infty$: for every fixed $c > 0$, the bound
$\mathrm{ex}(n, G_k) \ll n^{3/2 - c}$ fails for all sufficiently large $k$.
(Failure is upward-closed in $k$, since $G_k \subseteq G_{k+1}$ forces
$\mathrm{ex}(n, G_k) \le \mathrm{ex}(n, G_{k+1})$, so "for all sufficiently
large $k$" and "for infinitely many $k$" are equivalent here.)
-/
@[category research solved, AMS 5]
theorem erdos_1021.variants.subconstant_necessary :
    ∀ (c : ℝ), c > 0 →
    ∃ (K : ℕ), ∀ (k : ℕ), k ≥ K →
    ¬(∃ (C : ℝ), C > 0 ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ¬containsSubgraph G (subdivisionKComplete k) →
      (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - c)) := by
  sorry

end Erdos1021
