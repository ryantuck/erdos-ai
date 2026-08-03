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
# Erdős Problem 1015

*Reference:* [erdosproblems.com/1015](https://www.erdosproblems.com/1015)

Let $f(t, n)$ be minimal such that, in any two-colouring of the edges of $K_n$,
the vertices can be covered by vertex-disjoint monochromatic copies of $K_t$
(not necessarily the same colour) with at most $f(t, n)$ vertices remaining.
(The source page phrases this as "the edges can be partitioned into vertex
disjoint monochromatic copies of $K_t$"; the vertex-cover reading above is the
standard interpretation, following Moon [Mo66b].)

Estimate $f(t)$. In particular, is it true that $f(t)^{1/t} \to 1$? Is it true
that $f(t) \ll t$? Here $f(t)$ denotes the least bound valid for every
sufficiently large $n$.

A question of Moon [Mo66b], who proved that $f(3) = 4$, at least for $n \geq 8$.
Presumably Erdős intended to only ask this question for $n$ sufficiently large
depending on $t$. Erdős notes that $f(t) \ll 4^t$, by comparing to the Ramsey
number $R(t)$.

Burr, Erdős, and Spencer [BES75] proved that, for $n$ sufficiently large
depending on $t$,
$$
f(t, n) = R(t, t-1) + x(t, n),
$$
where $0 \leq x(t, n) < t$ is such that $n + 1 \equiv R(t, t-1) + x \pmod{t}$.

**Correction.** As printed on the source page, this formula cannot be exactly
right: any family of vertex-disjoint $K_t$'s covers a multiple of $t$ vertices,
so necessarily $f(t, n) \equiv n \pmod{t}$, whereas
$R(t, t-1) + x \equiv n + 1 \pmod{t}$. The formalization below states the
corrected form $f(t, n) = R(t, t-1) - 1 + x(t, n)$ (with the same $x$), which
is the unique value congruent to $n \bmod t$ in an interval of length $t$
around $R(t, t-1)$. Consistency checks: at $t = 2$ it gives the directly
verifiable $f(2, n) = n \bmod 2$ (every edge of $K_n$ is monochromatic, so one
greedily matches all but $n \bmod 2$ vertices; the printed formula gives
$1 + (n \bmod 2)$, off by exactly one), and at $t = 3$ it gives
$f(3, n) \in \{2, 3, 4\}$ with maximum $4$, matching Moon's $f(3) = 4$.

The problem is marked SOLVED on the source page (tooltip: "This has been
resolved in some other way than a proof or disproof"; accessed 2026-02-22):
[BES75] determines $f(t, n)$ up to the Ramsey number $R(t, t-1)$, which grows
exponentially in $t$, so both of the original questions have negative answers.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[Mo66b] Moon, J.W., _Disjoint triangles in chromatic graphs_. Math. Mag. (1966), 259-261.

[BES75] Burr, S.A., Erdős, P., Spencer, J.H., _Ramsey theorems for multiple copies of graphs_.
Trans. Amer. Math. Soc. (1975), 87-99.
-/

open Finset

namespace Erdos1015

/-- A set $S$ of vertices in `Fin n` is a monochromatic clique of colour $b$
under the edge-colouring $c$ if every pair of distinct vertices in $S$
has colour $b$. -/
def IsMonoClique (n : ℕ) (c : Fin n → Fin n → Bool) (S : Finset (Fin n))
    (b : Bool) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b

/-- The minimum number of leftover vertices $f(t, n)$: the smallest $r$ such
that for every symmetric 2-colouring of the edges of $K_n$, one can find
pairwise disjoint monochromatic $K_t$'s covering all but at most $r$
vertices. Note that every achievable leftover count equals $n - t \cdot k$
for some $k$, so $f(t, n) \equiv n \pmod{t}$. -/
noncomputable def minLeftover (t n : ℕ) : ℕ :=
  -- The infimum over r of: for every symmetric 2-colouring, one can cover
  -- all but at most r vertices by pairwise disjoint monochromatic K_t's.
  sInf {r : ℕ | ∀ (c : Fin n → Fin n → Bool), (∀ i j, c i j = c j i) →
    ∃ (cliques : Finset (Finset (Fin n))),
      (∀ S ∈ cliques, S.card = t) ∧
      (∀ S ∈ cliques, ∃ b : Bool, IsMonoClique n c S b) ∧
      (∀ S₁ ∈ cliques, ∀ S₂ ∈ cliques, S₁ ≠ S₂ → Disjoint S₁ S₂) ∧
      (univ \ cliques.biUnion id).card ≤ r}

/-- The 2-colour Ramsey number $R(s, t)$: the minimum $N$ such that every
symmetric 2-colouring of the edges of $K_N$ contains a monochromatic
clique of size $s$ in one colour or of size $t$ in the other. -/
noncomputable def ramseyNumber₂ (s t : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    (∃ S : Finset (Fin N), S.card = s ∧ IsMonoClique N c S false) ∨
    (∃ S : Finset (Fin N), S.card = t ∧ IsMonoClique N c S true)}

/--
Erdős Problem 1015 [Er71]:

For $t \geq 3$ and $n$ sufficiently large depending on $t$, the minimum number
of leftover vertices when covering any 2-coloured $K_n$ by vertex-disjoint
monochromatic $K_t$'s is exactly
$$
f(t, n) = R(t, t-1) - 1 + x,
$$
where $x \in \{0, \ldots, t-1\}$ satisfies $n + 1 \equiv R(t, t-1) + x
\pmod{t}$; equivalently, $f(t, n)$ is the unique integer congruent to $n$
modulo $t$ with $R(t, t-1) - 1 \leq f(t, n) \leq R(t, t-1) + t - 2$.

Proved by Burr, Erdős, and Spencer [BES75]. The source page prints the formula
as $f(t, n) = R(t, t-1) + x$, which is incompatible with the forced congruence
$f(t, n) \equiv n \pmod{t}$ and is provably off by one at $t = 2$, where
$f(2, n) = n \bmod 2$; see the module docstring for the correction and its
consistency checks. Since $R(t, t-1) \geq 1$, the natural-number subtraction
`- 1` is exact, and the subtraction `n + 1 - ramseyNumber₂ t (t - 1)` does not
truncate once $N₀$ exceeds $R(t, t-1)$.
-/
@[category research solved, AMS 5]
theorem erdos_1015 (t : ℕ) (ht : t ≥ 3) :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      minLeftover t n =
        ramseyNumber₂ t (t - 1) - 1 + (n + 1 - ramseyNumber₂ t (t - 1)) % t := by
  sorry

/--
Moon's result [Mo66b]: $f(3) = 4$, at least for $n \geq 8$ — that is, $4$ is
the least $r$ such that every 2-coloured $K_n$ with $n \geq 8$ can be covered
by vertex-disjoint monochromatic triangles with at most $r$ vertices left
over. (For a fixed $n$ the leftover count is congruent to $n$ modulo $3$, so
the pointwise statement "$f(3, n) = 4$ for all $n \geq 8$" is impossible;
$4$ is the maximum of $f(3, n) \in \{2, 3, 4\}$ over the residues of $n$.)
-/
@[category research solved, AMS 5]
theorem erdos_1015_moon :
    (∀ n ≥ 8, minLeftover 3 n ≤ 4) ∧
      ∀ r : ℕ, (∀ n ≥ 8, minLeftover 3 n ≤ r) → 4 ≤ r := by
  sorry

/--
The second of the two questions originally asked: "is it true that
$f(t) \ll t$?", i.e. is there a constant $C$ such that for every $t$ and all
sufficiently large $n$, all but at most $C \cdot t$ vertices can be covered by
vertex-disjoint monochromatic $K_t$'s? The answer is no: by [BES75],
eventually $f(t, n) \geq R(t, t-1) - 1$, which grows exponentially in $t$ by
the classical lower bound for Ramsey numbers.
-/
@[category research solved, AMS 5]
theorem erdos_1015.variants.linear_bound :
    answer(False) ↔
      ∃ C : ℕ, ∀ t ≥ 3, ∃ N₀ : ℕ, ∀ n ≥ N₀, minLeftover t n ≤ C * t := by
  sorry

/--
Erdős's observation [Er71]: $f(t) \ll 4^t$, by comparing to the Ramsey number
$R(t)$ — one can greedily extract monochromatic $K_t$'s as long as at least
$R(t, t) \leq 4^t$ vertices remain uncovered.
-/
@[category research solved, AMS 5]
theorem erdos_1015.variants.exponential_bound :
    ∃ C : ℕ, ∀ t ≥ 3, ∃ N₀ : ℕ, ∀ n ≥ N₀, minLeftover t n ≤ C * 4 ^ t := by
  sorry

end Erdos1015
