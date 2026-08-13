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
# Erdős Problem 1078

*Reference:* [erdosproblems.com/1078](https://www.erdosproblems.com/1078)

Let $G$ be an $r$-partite graph with $n$ vertices in each part. If $G$ has minimum degree
$\geq (r - \frac{3}{2} - o(1)) \cdot n$ then $G$ must contain a $K_r$.

A conjecture of Bollobás, Erdős, and Szemerédi [BES75b], who proved that $r - 3/2$ would be
the best possible here. This is true, and was proved by Haxell [Ha01]. The sharp threshold
of $(r-1)n - \lceil sn/(2s-1) \rceil$ where $s = \lfloor r/2 \rfloor$ was proved by Haxell
and Szabó [HaSz06].

The source page (edition 06 October 2025, accessed 2026-02-22) marks the problem PROVED
("This has been solved in the affirmative") and attaches the citation keys [BES75] and
[Er75] to the problem statement itself.

[BES75] Burr, S. A., Erdős, P., Spencer, J. H., _Ramsey theorems for multiple copies of
graphs_. Trans. Amer. Math. Soc. (1975), 87-99. (Bibliographic data for this site-wide key
recovered from the site's `/latex/1015` bibliography; the conjecture itself is posed in the
Bollobás–Erdős–Szemerédi paper cited here as [BES75b].)

[Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congressus
Numerantium (1975), 3-14. (Bibliographic data for this site-wide key recovered from the
site's `/latex/1079` bibliography.)

[BES75b] Bollobás, B., Erdős, P., and Szemerédi, E., proved that the threshold
$r - 3/2$ is best possible. (Full bibliographic data not recovered.)

[Ha01] Haxell, P., proved the conjecture. (Full bibliographic data not recovered.)

[HaSz06] Haxell, P. and Szabó, T., proved the sharp threshold of
$(r-1)n - \lceil sn/(2s-1) \rceil$ where $s = \lfloor r/2 \rfloor$. (Full bibliographic
data not recovered.)
-/

open SimpleGraph

namespace Erdos1078

/-- An $r$-partite graph on vertex set `Fin r × Fin n`: no edges within any part. -/
def IsMultipartite {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∀ (i : Fin r) (a b : Fin n), ¬G.Adj (i, a) (i, b)

/-- A transversal clique in an $r$-partite graph: a choice of one vertex from each
part such that all chosen vertices are pairwise adjacent. This corresponds
to a copy of $K_r$ in an $r$-partite graph. -/
def HasTransversalClique {r n : ℕ} (G : SimpleGraph (Fin r × Fin n)) : Prop :=
  ∃ f : Fin r → Fin n, ∀ i j : Fin r, i ≠ j → G.Adj (i, f i) (j, f j)

/--
Erdős Problem 1078 [BES75, Er75]:

Let $G$ be an $r$-partite graph with $n$ vertices in each part. If $G$ has minimum degree
$\geq (r - 3/2 - o(1)) \cdot n$ then $G$ must contain a $K_r$. (In an $r$-partite graph
any copy of $K_r$ is necessarily transversal, since no two of its vertices can share a
part.)

The $-o(1)$ slack is formalized as: there exists a fixed $\varepsilon > 0$ (which may
depend on $r$) such that for all sufficiently large $n$, minimum degree
$\geq (r - 3/2 - \varepsilon) n$ forces a transversal $K_r$. This is true: by [HaSz06]
the threshold is $(r-1)n - \lceil sn/(2s-1) \rceil \leq (r - 3/2)n - n/(2(2s-1))$ with
$s = \lfloor r/2 \rfloor$, so any $\varepsilon < 1/(2(2s-1))$ works. Quantifying instead
over every $\varepsilon > 0$ (the convention appropriate for $+o(1)$ slack above a
threshold) would be false here: for $\varepsilon \geq r$ the empty $r$-partite graph
satisfies the degree hypothesis vacuously yet contains no transversal $K_r$.

A conjecture of Bollobás, Erdős, and Szemerédi [BES75b], who proved that $r - 3/2$ is
best possible. Proved by Haxell [Ha01]. The sharp threshold of
$(r-1)n - \lceil sn/(2s-1) \rceil$ where $s = \lfloor r/2 \rfloor$ was proved by Haxell
and Szabó [HaSz06].
-/
@[category research solved, AMS 5]
theorem erdos_1078 (r : ℕ) (hr : r ≥ 2) :
    ∃ ε : ℝ, ε > 0 ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
    ∀ (G : SimpleGraph (Fin r × Fin n)) [DecidableRel G.Adj],
      IsMultipartite G →
      (∀ v : Fin r × Fin n, (G.degree v : ℝ) ≥ ((r : ℝ) - 3 / 2 - ε) * (n : ℝ)) →
      HasTransversalClique G := by
  sorry

/--
The sharp threshold, proved by Haxell and Szabó [HaSz06]: if $G$ is an $r$-partite graph
with $n \geq 1$ vertices in each part in which every vertex has degree strictly greater
than $(r-1)n - \lceil sn/(2s-1) \rceil$, where $s = \lfloor r/2 \rfloor$, then $G$
contains a transversal $K_r$.

The strict inequality is the correct reading of "threshold": for $r = 3$ the value is
$2n - n = n$, and the tripartite graph with parts $A$, $B$, $C$ in which $A$–$B$ and
$B$–$C$ are complete bipartite and $A$–$C$ is empty has minimum degree exactly $n$ and no
transversal triangle, so degree $\geq$ the threshold value does not suffice. The ceiling
$\lceil sn/(2s-1) \rceil$ is written as $(sn + 2s - 2)/(2s-1)$ in truncating
natural-number division (exact since $2s - 1 \geq 1$ for $r \geq 2$, and the outer
subtraction does not truncate since $\lceil sn/(2s-1) \rceil \leq sn \leq (r-1)n$).
-/
@[category research solved, AMS 5]
theorem erdos_1078.variants.sharp_threshold (r n : ℕ) (hr : r ≥ 2) (hn : n ≥ 1)
    (G : SimpleGraph (Fin r × Fin n)) [DecidableRel G.Adj]
    (hG : IsMultipartite G)
    (hdeg : ∀ v : Fin r × Fin n,
      G.degree v > (r - 1) * n - (r / 2 * n + 2 * (r / 2) - 2) / (2 * (r / 2) - 1)) :
    HasTransversalClique G := by
  sorry

end Erdos1078
