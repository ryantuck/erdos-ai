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
# Erdős Problem 1020

Conjecture on the maximum number of edges in an $r$-uniform hypergraph on $n$ vertices
containing no matching of size $k$ (the Erdős Matching Conjecture).

The two terms in the conjectured maximum correspond to two extremal constructions:
(1) taking all $r$-subsets of a fixed set of $rk - 1$ vertices (clique construction), and
(2) taking all $r$-subsets that intersect a fixed set of $k - 1$ vertices (star/covering
construction).

The source page states the identity for all $r \geq 3$ with no constraint on $n$, but the
literal equality fails whenever $k \geq 2$ and $n < rk - 1$: there every $r$-uniform
hypergraph on $n$ vertices is matching-free (a $k$-matching needs $rk > n$ vertices), so
the maximum is $\binom{n}{r}$, strictly smaller than the first term $\binom{rk-1}{r}$ (e.g.
$n = 4$, $r = 3$, $k = 2$: maximum $\binom{4}{3} = 4$ but the formula gives
$\binom{5}{3} = 10$). The page's own remark that the conjecture is "trivially true if
$n < kr$" refers to the upper-bound reading, formalized in
`erdos_1020.variants.upper_bound`; the equality is stated here for $n \geq rk - 1$.

Status on the source page: **open** ("FALSIFIABLE: Open, but could be disproved with a
finite counterexample"). Erdős and Gallai [ErGa59] proved the case $r = 2$ (which also
follows from the Erdős–Ko–Rado theorem). Frankl [Fr87] proved
$f(n;r,k) \leq (k-1)\binom{n-1}{r-1}$. The second term in the maximum dominates when
$n \geq (r+1)k$. Among many partial results: the conjecture holds trivially for $n < kr$;
for $n = kr$ (Kleitman [Kl68]); for $kr \leq n \leq k(r + \frac{1}{2r^{2r+1}})$ (Frankl
[Fr17]); for $r \geq 5$, $k > 101r^3$, $kr \leq n < k(r + \frac{1}{100r})$ (Kolupaev and
Kupavskii [KoKu23]); for $n > kc_r$ (Erdős [Er65d]); for $n > 100k^2r$ (Frankl and Füredi
[Fr87]); for $n \geq 2kr^3$ (Bollobás, Daykin, and Erdős [BDE76]); for $r = 3$ and
$n \geq 4k$ (Frankl, Rödl, and Ruciński [FRR12]); for $n \geq 3kr^2$ (Huang, Loh, and
Sudakov [HLS12]); for $n > 2k\frac{r^2}{\log r}$ (Frankl, Łuczak, and Mieczkowska
[FLM12]); and for $r = 3$ and all $k$ (Łuczak and Mieczkowska [LuMi14]).

*Reference:* [erdosproblems.com/1020](https://www.erdosproblems.com/1020)
(page last edited 28 December 2025, accessed 2026-02-22).

[Er65d] Erdős, P., *A problem on independent r-tuples*, Ann. Univ. Sci. Budapest. Eötvös Sect.
Math. 8 (1965), 93–95.

[Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*,
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.

[ErGa59] Erdős, P. and Gallai, T., 1959. (Bibliographic details not recoverable offline.)

[Kl68] Kleitman, D., 1968. (Bibliographic details not recoverable offline.)

[BDE76] Bollobás, B., Daykin, D. E. and Erdős, P., 1976. (Details not recoverable offline.)

[Fr87] Frankl, P., 1987. (The source page cites this key both for Frankl's bound and for a
Frankl–Füredi result; bibliographic details not recoverable offline.)

[FRR12] Frankl, P., Rödl, V. and Ruciński, A., 2012. (Details not recoverable offline.)

[HLS12] Huang, H., Loh, P. and Sudakov, B., 2012. (Details not recoverable offline.)

[FLM12] Frankl, P., Łuczak, T. and Mieczkowska, K., 2012. (Details not recoverable offline.)

[LuMi14] Łuczak, T. and Mieczkowska, K., 2014. (Details not recoverable offline.)

[Fr17] Frankl, P., 2017. (Bibliographic details not recoverable offline.)

[KoKu23] Kolupaev, D. and Kupavskii, A., 2023. (Details not recoverable offline.)
-/

open Finset

namespace Erdos1020

/-- An $r$-uniform hypergraph on vertex set `Fin n`: every edge has exactly $r$ vertices. -/
def IsRUniform {n : ℕ} (H : Finset (Finset (Fin n))) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A matching of size $k$ in a hypergraph: $k$ pairwise vertex-disjoint edges. -/
def HasMatching {n : ℕ} (H : Finset (Finset (Fin n))) (k : ℕ) : Prop :=
  ∃ M : Finset (Finset (Fin n)), M ⊆ H ∧ M.card = k ∧
    ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- `maxEdgesNoMatching n r k` is the maximum number of edges in an $r$-uniform hypergraph
on $n$ vertices that contains no matching of size $k$. -/
noncomputable def maxEdgesNoMatching (n r k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)),
    IsRUniform H r ∧ ¬HasMatching H k ∧ H.card = m}

/--
Erdős Problem 1020 (Erdős Matching Conjecture) [Er65d], [Er71, p.103]:

For all $r \geq 3$ and $n \geq rk - 1$, the maximum number of edges in an $r$-uniform
hypergraph on $n$ vertices containing no matching of size $k$ equals
$$
  \max\left(\binom{rk-1}{r},\; \binom{n}{r} - \binom{n-k+1}{r}\right).
$$

The hypothesis $n \geq rk - 1$ does not appear on the source page but is necessary: for
$k \geq 2$ and $n < rk - 1$ the left-hand side is $\binom{n}{r}$ (every hypergraph is
matching-free) while the right-hand side is $\binom{rk-1}{r} > \binom{n}{r}$; e.g. $n = 4$,
$r = 3$, $k = 2$ gives $4 \neq 10$. See `erdos_1020.variants.upper_bound` for the form
of the conjecture valid for all $n$.
-/
@[category research open, AMS 5]
theorem erdos_1020 (n r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1) (hn : n ≥ r * k - 1) :
    maxEdgesNoMatching n r k =
      max (Nat.choose (r * k - 1) r) (Nat.choose n r - Nat.choose (n - k + 1) r) := by
  sorry

/--
The Erdős Matching Conjecture in upper-bound form, valid for all $n$: an $r$-uniform
hypergraph on $n$ vertices with no matching of size $k$ has at most
$\max\left(\binom{rk-1}{r}, \binom{n}{r} - \binom{n-k+1}{r}\right)$ edges. This is the
reading under which the source page's remark "the conjecture is trivially true if
$n < kr$" holds (for $n \leq rk - 1$ the maximum is $\binom{n}{r} \leq \binom{rk-1}{r}$);
combined with the two extremal constructions it is equivalent to the conjecture.
-/
@[category research open, AMS 5]
theorem erdos_1020.variants.upper_bound (n r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1) :
    maxEdgesNoMatching n r k ≤
      max (Nat.choose (r * k - 1) r) (Nat.choose n r - Nat.choose (n - k + 1) r) := by
  sorry

/--
The case $r = 2$ of the Erdős Matching Conjecture, proved by Erdős and Gallai [ErGa59]
(it also follows from the Erdős–Ko–Rado theorem): the maximum number of edges in a graph
on $n \geq 2k - 1$ vertices with no matching of size $k$ is
$\max\left(\binom{2k-1}{2}, \binom{n}{2} - \binom{n-k+1}{2}\right)$.
-/
@[category research solved, AMS 5]
theorem erdos_1020.variants.r_eq_two (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 2 * k - 1) :
    maxEdgesNoMatching n 2 k =
      max (Nat.choose (2 * k - 1) 2) (Nat.choose n 2 - Nat.choose (n - k + 1) 2) := by
  sorry

/--
The case $n = rk$ of the Erdős Matching Conjecture, proved by Kleitman [Kl68].
-/
@[category research solved, AMS 5]
theorem erdos_1020.variants.kleitman (r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1) :
    maxEdgesNoMatching (r * k) r k =
      max (Nat.choose (r * k - 1) r)
        (Nat.choose (r * k) r - Nat.choose (r * k - k + 1) r) := by
  sorry

/--
Frankl's bound [Fr87]: an $r$-uniform hypergraph on $n$ vertices with no matching of size
$k$ has at most $(k-1)\binom{n-1}{r-1}$ edges.

The source page states the bound with no constraint on $n$, but it fails for small $n$
(e.g. $n = 5$, $r = 3$, $k = 2$: the complete hypergraph has $\binom{5}{3} = 10$ edges
and no $2$-matching, but $(k-1)\binom{4}{2} = 6$). It is stated here for $n \geq rk$,
where it is tight at $n = rk$ (both sides equal $\binom{rk-1}{r} = (k-1)\binom{rk-1}{r-1}$
by Kleitman's theorem); the precise range of validity in [Fr87] is not recoverable
offline.
-/
@[category research solved, AMS 5]
theorem erdos_1020.variants.frankl_bound (n r k : ℕ) (hr : r ≥ 3) (hk : k ≥ 1)
    (hn : n ≥ r * k) :
    maxEdgesNoMatching n r k ≤ (k - 1) * Nat.choose (n - 1) (r - 1) := by
  sorry

/--
The case $r = 3$, $n \geq 4k$ of the Erdős Matching Conjecture, proved by Frankl, Rödl,
and Ruciński [FRR12].
-/
@[category research solved, AMS 5]
theorem erdos_1020.variants.r_eq_three_large_n (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ 4 * k) :
    maxEdgesNoMatching n 3 k =
      max (Nat.choose (3 * k - 1) 3) (Nat.choose n 3 - Nat.choose (n - k + 1) 3) := by
  sorry

end Erdos1020
