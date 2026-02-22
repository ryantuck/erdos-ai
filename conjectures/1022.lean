import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1022

Is there a constant $c_t$, where $c_t \to \infty$ as $t \to \infty$, such that
if $\mathcal{F}$ is a finite family of finite sets, all of size at least $t$,
and for every set $X$ there are $< c_t |X|$ many $A \in \mathcal{F}$ with
$A \subseteq X$, then $\mathcal{F}$ has chromatic number $2$ (property B)?

This is false, and $c_t < 2$ for all $t$: a counterexample is provided by
Wood [Wo13b], who constructs, for any $r \geq 2$, a triangle-free
2-degenerate $r$-uniform hypergraph with chromatic number 3.
-/

/-- A finite set family has **property B** (is 2-colorable) if there exists
    a 2-coloring of the ground set such that no edge is monochromatic:
    every edge contains elements of both colors. -/
def HasPropertyB {n : ℕ} (F : Finset (Finset (Fin n))) : Prop :=
  ∃ f : Fin n → Bool, ∀ e ∈ F, (∃ v ∈ e, f v = true) ∧ (∃ v ∈ e, f v = false)

/--
**Erdős Problem #1022** [Er71, p.105]:

There does NOT exist a function $c : \mathbb{N} \to \mathbb{R}$ with
$c(t) \to \infty$ as $t \to \infty$ such that the following holds: for every
$t$ and every finite hypergraph $\mathcal{F}$ on $n$ vertices, if all edges
have size $\geq t$ and for every vertex set $X$ the number of edges contained
in $X$ is $< c(t) \cdot |X|$, then $\mathcal{F}$ has property B.

Disproved by Wood [Wo13b].
-/
theorem erdos_problem_1022 :
    ¬ ∃ (c : ℕ → ℝ), Tendsto c atTop atTop ∧
      ∀ (t : ℕ) (n : ℕ) (F : Finset (Finset (Fin n))),
        (∀ e ∈ F, t ≤ e.card) →
        (∀ X : Finset (Fin n),
          ((F.filter (fun e => e ⊆ X)).card : ℝ) < c t * (X.card : ℝ)) →
        HasPropertyB F :=
  sorry

end
