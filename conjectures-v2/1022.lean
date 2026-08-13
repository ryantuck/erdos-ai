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
# Erdős Problem 1022

*Reference:* [erdosproblems.com/1022](https://www.erdosproblems.com/1022)

Is there a constant $c_t$, where $c_t \to \infty$ as $t \to \infty$, such that if
$\mathcal{F}$ is a finite family of finite sets, all of size at least $t$, and for every
set $X$ there are $< c_t |X|$ many $A \in \mathcal{F}$ with $A \subseteq X$, then
$\mathcal{F}$ has chromatic number $2$ (in other words, has property B)?

Erdős originally conjectured, in this language, that $c_2 = 1$, which he reports in
[Er71] was proved by Lovász. He seems to refer to [Lo68] for this, which does not
contain this result, so presumably this is a miscitation and perhaps Lovász reported
the easy proof that $c_2 = 1$ (see the comment by Tao on the problem page) directly to
Erdős.

The condition on $c_t$ is a weaker form of the condition that the hypergraph is
degenerate: a hypergraph is $d$-degenerate if every subhypergraph has a vertex contained
in at most $d$ edges, which implies that for any $X$ there are at most $d|X|$ many edges
contained in $X$.

The answer is no, and $c_t < 2$ for all $t$: a counterexample is provided by Wood
[Wo13b], who constructs, for any $r \geq 2$, a triangle-free $2$-degenerate $r$-uniform
hypergraph with chromatic number $3$. A similar counterexample was found independently
by KoishiChan in the comments on the problem page.

The erdosproblems.com page (edition of 25 January 2026, accessed 2026-02-22) lists the
problem as PROVED (LEAN), i.e. the resolution has also been verified in Lean; the
verification link is not recorded in the archived page, so the category tag below
remains `research solved`.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[Lo68] Lovász, L., _On covering of graphs_. Theory of Graphs (Proc. Colloq., Tihany, 1966)
(1968), 231-236.

[Wo13b] Wood, D.R., _Hypergraph colouring and degeneracy_. arXiv:1310.2972 (2013).
-/

open Finset Filter

namespace Erdos1022

/-- A finite set family has **property B** (is 2-colorable) if there exists
    a 2-coloring of the ground set such that no edge is monochromatic:
    every edge contains elements of both colors. -/
def HasPropertyB {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∃ f : Fin n → Bool, ∀ e ∈ F, (∃ v ∈ e, f v = true) ∧ (∃ v ∈ e, f v = false)

/--
**Erdős Problem 1022** [Er71, p.105]:

Is there a constant $c_t$, where $c_t \to \infty$ as $t \to \infty$, such that if
$\mathcal{F}$ is a finite family of finite sets, all of size at least $t$, and for
every set $X$ at most $c_t |X|$ many $A \in \mathcal{F}$ satisfy $A \subseteq X$,
then $\mathcal{F}$ has property B?

The answer is no (`answer(False)`): disproved by Wood [Wo13b], who shows $c_t < 2$
for all $t$.

Note: the source states the density hypothesis with a strict inequality
($< c_t |X|$). It is stated here with $\leq$ so that the case $X = \emptyset$
(where the strict form reads $0 < 0$ and is unsatisfiable, making the hypothesis
vacuous) does not trivialize the statement. For nonempty $X$ the two forms are
interchangeable up to rescaling $c$, which does not affect the existence of such
a $c$.
-/
@[category research solved, AMS 5]
theorem erdos_1022 : answer(False) ↔
    ∃ (c : ℕ → ℝ), Tendsto c atTop atTop ∧
      ∀ (t : ℕ) (n : ℕ) (F : Finset (Finset (Fin n))),
        (∀ e ∈ F, t ≤ e.card) →
        (∀ X : Finset (Fin n),
          ((F.filter (fun e => e ⊆ X)).card : ℝ) ≤ c t * (X.card : ℝ)) →
        HasPropertyB F := by sorry

/--
Erdős originally conjectured, in this language, that $c_2 = 1$, which he reports in
[Er71] was proved by Lovász (the reference [Lo68] he seems to cite for this does not
contain the result, so it was presumably communicated directly): a finite family of
finite sets, all of size at least $2$, such that every nonempty set $X$ contains fewer
than $|X|$ members of the family, has property B.

The hypothesis is restricted to nonempty $X$ since for $X = \emptyset$ the strict
inequality $0 < 0$ would be unsatisfiable.
-/
@[category research solved, AMS 5]
theorem erdos_1022.variants.lovasz_c_two {n : ℕ} (F : Finset (Finset (Fin n)))
    (hcard : ∀ e ∈ F, 2 ≤ e.card)
    (hdeg : ∀ X : Finset (Fin n), 0 < X.card →
      (F.filter (fun e => e ⊆ X)).card < X.card) :
    HasPropertyB F := by sorry

/--
Wood [Wo13b] constructs, for any $r \geq 2$, a (moreover triangle-free) $2$-degenerate
$r$-uniform hypergraph with chromatic number $3$. Since $d$-degeneracy implies that any
set $X$ contains at most $d|X|$ edges, this shows $c_t < 2$ for all $t$ in the language
of the main problem: for every $t \geq 2$ there is a $t$-uniform finite family in which
every set $X$ contains at most $2|X|$ members, yet which does not have property B. (The
triangle-free property of the construction is not encoded here.)
-/
@[category research solved, AMS 5]
theorem erdos_1022.variants.wood_counterexample :
    ∀ t : ℕ, 2 ≤ t →
      ∃ (n : ℕ) (F : Finset (Finset (Fin n))),
        (∀ e ∈ F, e.card = t) ∧
        (∀ X : Finset (Fin n), (F.filter (fun e => e ⊆ X)).card ≤ 2 * X.card) ∧
        ¬ HasPropertyB F := by sorry

end Erdos1022
