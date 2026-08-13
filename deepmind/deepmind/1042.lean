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
# Erdős Problem 1042

*Reference:* [erdosproblems.com/1042](https://www.erdosproblems.com/1042)

Let $F \subset \mathbb{C}$ be a closed set of transfinite diameter $1$ which is not
contained in any closed disc of radius $1$. If $f(z) = \prod_{i=1}^n (z - z_i) \in
\mathbb{C}[x]$ with all $z_i \in F$, then can $\{z : |f(z)| < 1\}$ have $n$ connected
components?

If the transfinite diameter of $F$ is $< 1$ then must this set only have at most
$(1-c)n$ connected components, where $c > 0$ depends only on $F$ (or just the
transfinite diameter of $F$)?

A problem of Erdős, Herzog, and Piranian [EHP58, p.139], who proved that if $F$ is
the disc of radius $1$ then this set can have $n$ connected components (for example
$f(z) = z^n + 1$).

This was solved (both questions answered in the affirmative) by Ghosh and
Ramachandran [GhRa24], who proved that, if $d$ is the transfinite diameter of $F$,
then:
- if $0 < d < 1$ then the set has at most $(1-c)n$ connected components for some
  $c > 0$ depending on $F$;
- if $d \leq 1/4$ and $F$ is connected then the set has only one connected
  component;
- there are examples with $d = 1$ such that, for infinitely many $n$, the set can
  have $n$ connected components.

They also note that the answer cannot depend only on the transfinite diameter of
$F$: both $F_1 = \{z : |z| \leq 1/2\}$ and $F_2 = [-1, 1]$ have transfinite diameter
$1/2$, but the former always has one connected component, while the latter can have
$\gg n$ many connected components.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of
polynomials_, J. Analyse Math. 6 (1958), 125-148.

[GhRa24] Ghosh and Ramachandran, solved both parts of this problem (2024). (The
source page provides no further bibliographic details — no first names, title, or
venue — so none are recorded here.)
-/

open Classical Filter Finset

namespace Erdos1042

/-- The product of pairwise distances $\prod_{i<j} \|z_i - z_j\|$ for a tuple of
complex numbers. -/
noncomputable def pairwiseDistProd {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The $n$-th transfinite diameter of $F \subseteq \mathbb{C}$:
$$d_n(F) = \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{2/(n(n-1))}.$$ -/
noncomputable def nthTransfiniteDiam (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of $F \subseteq \mathbb{C}$:
$$\rho(F) = \lim_{n \to \infty} d_n(F).$$

Note on degenerate inputs: for unbounded $F$ (true transfinite diameter $\infty$)
the sets defining $d_n(F)$, $n \geq 2$, are unbounded above and `Real`'s `sSup`
returns the junk value $0$, so this encoding evaluates to $0$; likewise for
$F = \emptyset$. Hypotheses of the form `0 < transfiniteDiameter F` therefore
restrict attention to bounded (hence compact) nonempty closed sets, for which
$d_n(F)$ is non-increasing in $n \geq 2$ and the limit is genuine. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam F n))

/-- The sublevel set $\{z : \|\prod_i(z - z_i)\| < 1\}$ of a monic polynomial with
given roots. -/
def sublevelSet {n : ℕ} (z : Fin n → ℂ) : Set ℂ :=
  {w : ℂ | ‖(univ : Finset (Fin n)).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem 1042, first question [EHP58, p.139]:

Can $\{z : |\prod(z - z_i)| < 1\}$ have $n$ connected components, for roots
$z_1, \ldots, z_n$ in a closed set $F \subset \mathbb{C}$ of transfinite diameter $1$
which is not contained in any closed disc of radius $1$?

Solved in the affirmative by Ghosh and Ramachandran [GhRa24], who constructed a
closed set $F$ with transfinite diameter $1$, not contained in any closed disc of
radius $1$, such that for infinitely many $n$ there exist $z_1,\ldots,z_n \in F$ for
which $\{z : |\prod(z - z_i)| < 1\}$ has exactly $n$ connected components; hence
`answer(True)`.

(The degenerate index $n = 0$ — empty product, empty sublevel set, $0$ components —
belongs to the displayed set trivially, which does not affect `Set.Infinite`.)
-/
@[category research solved, AMS 30 31]
theorem erdos_1042 : answer(True) ↔
    ∃ (F : Set ℂ), IsClosed F ∧ transfiniteDiameter F = 1 ∧
      (¬∃ c : ℂ, F ⊆ Metric.closedBall c 1) ∧
      Set.Infinite {n : ℕ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
        Nat.card (ConnectedComponents ↥(sublevelSet z)) = n} := by
  sorry

/--
Erdős Problem 1042, second question:

If the transfinite diameter of the closed set $F \subset \mathbb{C}$ is $< 1$, must
$\{z : |\prod(z - z_i)| < 1\}$ have at most $(1-c)n$ connected components, where
$c > 0$ depends only on $F$?

Solved in the affirmative by Ghosh and Ramachandran [GhRa24] for
$0 < \text{transfinite diameter} < 1$: there exists $c > 0$ (depending on $F$) such
that for all sufficiently large $n$ and all $z_1,\ldots,z_n \in F$, the number of
connected components of $\{z : |\prod(z - z_i)| < 1\}$ is at most $(1-c) \cdot n$;
hence `answer(True)`.

The bound is asserted for all sufficiently large $n$ only: for $n = 1$ the sublevel
set is an open disc of radius $1$ with exactly one connected component, and
$1 \leq (1-c) \cdot 1$ fails for every $c > 0$, so the literal "for all $n$" form is
false. The hypothesis $0 < \text{transfinite diameter}$ matches the solved result as
stated on the source page; under this encoding it also excludes unbounded $F$, for
which `transfiniteDiameter` returns the junk value $0$ (see its docstring).
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.upper_bound : answer(True) ↔
    ∀ (F : Set ℂ), IsClosed F →
      0 < transfiniteDiameter F → transfiniteDiameter F < 1 →
      ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop, ∀ z : Fin n → ℂ, (∀ i, z i ∈ F) →
        (Nat.card (ConnectedComponents ↥(sublevelSet z)) : ℝ) ≤ (1 - c) * n := by
  sorry

/--
Erdős Problem 1042, connected unique component [GhRa24]:

If $F \subset \mathbb{C}$ is closed, connected, and has transfinite diameter at most $1/4$, then
for all $n \geq 1$ and all $z_1,\ldots,z_n \in F$, the sublevel set $\{z : |\prod(z - z_i)| < 1\}$
has exactly one connected component.

(The hypothesis $0 < n$ excludes the degenerate case $n = 0$, where the empty
product gives $f \equiv 1$, the sublevel set is empty, and the number of connected
components is $0$, not $1$.)
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.connected_unique_component (F : Set ℂ) (hF : IsClosed F)
    (hconn : IsConnected F) (hd : transfiniteDiameter F ≤ 1 / 4) :
    ∀ (n : ℕ) (z : Fin n → ℂ), 0 < n → (∀ i, z i ∈ F) →
      Nat.card (ConnectedComponents ↥(sublevelSet z)) = 1 := by
  sorry

/--
Erdős Problem 1042, unit disc example [EHP58]:

Erdős, Herzog, and Piranian proved that if $F$ is the closed disc of radius $1$
(transfinite diameter $1$, but trivially contained in a closed disc of radius $1$),
then for every $n$ the set $\{z : |\prod(z - z_i)| < 1\}$ can have $n$ connected
components — for example $f(z) = z^n + 1$, whose roots are the $n$-th roots of $-1$.
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.unit_disc :
    ∀ n : ℕ, ∃ z : Fin n → ℂ, (∀ i, z i ∈ Metric.closedBall 0 1) ∧
      Nat.card (ConnectedComponents ↥(sublevelSet z)) = n := by
  sorry

/--
Erdős Problem 1042, transfinite diameter alone does not decide, part I [GhRa24]:

Ghosh and Ramachandran note that $F_1 = \{z : |z| \leq 1/2\}$ has transfinite
diameter $1/2$, yet for every $n \geq 1$ and all roots $z_1, \ldots, z_n \in F_1$ the
set $\{z : |\prod(z - z_i)| < 1\}$ always has exactly one connected component.
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.half_disc :
    ∀ (n : ℕ) (z : Fin n → ℂ), 0 < n → (∀ i, z i ∈ Metric.closedBall 0 (1 / 2)) →
      Nat.card (ConnectedComponents ↥(sublevelSet z)) = 1 := by
  sorry

/--
Erdős Problem 1042, transfinite diameter alone does not decide, part II [GhRa24]:

Ghosh and Ramachandran note that $F_2 = [-1, 1]$ also has transfinite diameter
$1/2$, yet the set $\{z : |\prod(z - z_i)| < 1\}$ can have $\gg n$ many connected
components: there is a constant $c > 0$ such that for infinitely many $n$ some
$z_1, \ldots, z_n \in [-1, 1]$ give at least $c \cdot n$ connected components.
-/
@[category research solved, AMS 30 31]
theorem erdos_1042.variants.segment :
    ∃ c : ℝ, c > 0 ∧ Set.Infinite {n : ℕ | ∃ z : Fin n → ℂ,
      (∀ i, z i ∈ {w : ℂ | w.im = 0 ∧ w.re ∈ Set.Icc (-1 : ℝ) 1}) ∧
      c * n ≤ (Nat.card (ConnectedComponents ↥(sublevelSet z)) : ℝ)} := by
  sorry

end Erdos1042
