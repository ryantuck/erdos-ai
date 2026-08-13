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
# Erdős Problem 1066

*Reference:* [erdosproblems.com/1066](https://www.erdosproblems.com/1066)

Let $G$ be a graph given by $n$ points in $\mathbb{R}^2$, where any two distinct points are
at least distance $1$ apart, and we draw an edge between two points if they are
distance $1$ apart.

Let $g(n)$ be maximal such that any such graph always has an independent set on
at least $g(n)$ vertices. Estimate $g(n)$, or perhaps $\lim g(n)/n$.

The problem is [Er87b, p.171]; it is OPEN (erdosproblems.com, page edition
02 October 2025).

Such graphs are always planar. Erdős initially thought that $g(n) = n/3$, but Chung and
Graham, and independently Pach, gave a construction showing $g(n) \leq \frac{6}{19}n$,
and Pach and Tóth [PaTo96] improved this to $g(n) \leq \frac{5}{16}n$. Pollack [Po85]
noted that the four colour theorem implies $g(n) \geq n/4$, since the graph is planar;
this lower bound was improved to $\frac{9}{35}n$ by Csizmadia [Cs98] and then to
$\frac{8}{31}n$ by Swanepoel [Sw02]. The current record bounds are
$$\frac{8}{31}n \leq g(n) \leq \frac{5}{16}n.$$
The lower bound is due to Swanepoel [Sw02] and the upper bound to Pach and
Tóth [PaTo96].

Pollack [Po85] also reports a letter of Erdős posing the higher-dimensional
generalisation: given $n$ points in $\mathbb{R}^d$ with minimum distance $1$, let $g_d(n)$
be maximal such that there always exist at least $g_d(n)$ of the points with pairwise
distances $> 1$. Is it true that $g_d(n) \gg n/d$ in general? (The upper bound
$g_d(n) \ll n/d$ is trivial, considering widely spaced unit simplices.)

See [erdosproblems.com/1070](https://www.erdosproblems.com/1070) for the independence
number of general unit distance graphs, without the minimum-distance separation.

[Er87b] Erdős, P., *Some combinatorial and metric problems in geometry*. Intuitive
geometry (Siófok, 1985) (1987), 167-177.

[Po85] Pollack, R., *Increasing the minimum distance of a set of points*. J. Combin.
Theory Ser. A (1985), 450.

[Cs98] Csizmadia, G., *On the independence number of minimum distance graphs*.
Discrete & Computational Geometry (1998), 179-187.

[Sw02] Swanepoel, K., *Independence numbers of planar contact graphs*.
Discrete & Computational Geometry 28 (2002), 649-670.

[PaTo96] Pach, J. and Tóth, G., *On the independence number of coin graphs*.
Geombinatorics 6 (1996), 30-33.
-/

namespace Erdos1066

/--
**Erdős Problem 1066**, lower bound [Sw02]:

For every $n \geq 1$ and every injective placement of $n$ points in $\mathbb{R}^2$ with all
pairwise distances $\geq 1$, there exists a set of at least $\frac{8}{31}n$ points with
no two at distance exactly $1$ (an independent set in the unit distance graph).
-/
@[category research solved, AMS 5 52]
theorem erdos_1066 (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2))
    (hf_inj : Function.Injective f)
    (hf_min : ∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 8 / 31 * (n : ℝ) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem 1066**, upper bound [PaTo96]:

For all sufficiently large $n$, there exists an injective placement of $n$ points
in $\mathbb{R}^2$ with all pairwise distances $\geq 1$ such that every independent set in the
unit distance graph has size at most $\frac{5}{16}n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.upper_bound :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        Function.Injective f ∧
        (∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) ∧
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ 5 / 16 * (n : ℝ) := by
  sorry

/--
**Erdős Problem 1066**, four colour theorem lower bound [Po85]:

For every $n \geq 1$ and every injective placement of $n$ points in $\mathbb{R}^2$ with all
pairwise distances $\geq 1$, there exists a set of at least $\frac{n}{4}$ points with no
two at distance exactly $1$. Pollack [Po85] noted this follows from the four colour
theorem, since such unit distance graphs are planar; Pach observed that for these
graphs four-colourability admits a simple inductive proof.
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.four_color_lower (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2))
    (hf_inj : Function.Injective f)
    (hf_min : ∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ (n : ℝ) / 4 ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem 1066**, Csizmadia's lower bound [Cs98]:

For every $n \geq 1$ and every injective placement of $n$ points in $\mathbb{R}^2$ with all
pairwise distances $\geq 1$, there exists a set of at least $\frac{9}{35}n$ points with
no two at distance exactly $1$. This improved Pollack's $n/4$ bound and was later
superseded by Swanepoel's $\frac{8}{31}n$ (the main statement `erdos_1066`).
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.csizmadia_lower (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2))
    (hf_inj : Function.Injective f)
    (hf_min : ∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 9 / 35 * (n : ℝ) ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem 1066**, Chung–Graham/Pach upper bound:

For all sufficiently large $n$, there exists an injective placement of $n$ points
in $\mathbb{R}^2$ with all pairwise distances $\geq 1$ such that every independent set in
the unit distance graph has size at most $\frac{6}{19}n$. This construction, found by
Chung and Graham and independently by Pach (no separate reference is given on the
problem page), disproved Erdős's initial guess that $g(n) = n/3$; it was later
improved to $\frac{5}{16}n$ by Pach and Tóth [PaTo96].
-/
@[category research solved, AMS 5 52]
theorem erdos_1066.variants.chung_graham_pach_upper :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        Function.Injective f ∧
        (∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) ∧
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ 6 / 19 * (n : ℝ) := by
  sorry

/--
**Erdős Problem 1066**, higher-dimensional generalisation [Po85]:

Pollack [Po85] reports a letter of Erdős posing the following: given $n$ points in
$\mathbb{R}^d$ with minimum distance $1$, let $g_d(n)$ be maximal such that there always
exist at least $g_d(n)$ of the points with pairwise distances $> 1$. Is it true that
$g_d(n) \gg n/d$ in general, i.e. with an absolute constant uniform in $d$? (Since all
pairwise distances are $\geq 1$, "distance $> 1$" coincides with "distance $\neq 1$",
so this is the independent-set notion of the main statement.) The upper bound
$g_d(n) \ll n/d$ is trivial, considering widely spaced unit simplices.
-/
@[category research open, AMS 5 52]
theorem erdos_1066.variants.higher_dimensional : answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 1 → ∀ n : ℕ, n ≥ 1 →
      ∀ f : Fin n → EuclideanSpace ℝ (Fin d),
        Function.Injective f →
        (∀ i j : Fin n, i ≠ j → dist (f i) (f j) ≥ 1) →
        ∃ S : Finset (Fin n),
          (S.card : ℝ) ≥ c * (n : ℝ) / (d : ℝ) ∧
          ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) > 1 := by
  sorry

end Erdos1066
