import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.RelClasses

open SimpleGraph Cardinal Ordinal

noncomputable section

/-!
# Erdős Problem #919

Is there a graph $G$ with vertex set $\omega_2^2$ and chromatic number $\aleph_2$
such that every subgraph whose vertices have a lesser type has chromatic number
$\leq \aleph_0$?

What if instead we ask for $G$ to have chromatic number $\aleph_1$?

This question was inspired by a theorem of Babai, that if $G$ is a graph on a
well-ordered set with chromatic number $\geq \aleph_0$ there is a subgraph on
vertices with order-type $\omega$ with chromatic number $\aleph_0$.

Erdős and Hajnal showed this does not generalise to higher cardinals — they
constructed a graph on $\omega_1^2$ with chromatic number $\aleph_1$ such that
every strictly smaller subgraph has chromatic number $\leq \aleph_0$.

A similar construction produces a graph on $\omega_2^2$ with chromatic number
$\aleph_2$ such that every smaller subgraph has chromatic number $\leq \aleph_1$.

https://www.erdosproblems.com/919
Tags: graph theory, chromatic number
-/

/--
Erdős Problem #919, Part 1 [Er69b]:

Is there a graph on a well-ordered set of order type ω₂ · ω₂ with chromatic
number ℵ₂ such that every subgraph induced on a subset of strictly smaller
order type has chromatic number ≤ ℵ₀?

The chromatic number condition is expressed as: any proper coloring of G
requires at least ℵ₂ colors, while every induced subgraph on a subset of
smaller order type admits a proper coloring with countably many (ℕ) colors.
-/
theorem erdos_problem_919_part1 :
    ∃ (V : Type) (_ : LinearOrder V) (_ : IsWellOrder V (· < ·))
      (G : SimpleGraph V),
      -- The order type of V is ω₂ · ω₂
      Ordinal.type ((· < ·) : V → V → Prop) =
        Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) ∧
      -- G has chromatic number ≥ ℵ₂ (any proper coloring needs ≥ ℵ₂ colors)
      (∀ (α : Type), Nonempty (G.Coloring α) → aleph 2 ≤ #α) ∧
      -- Every induced subgraph on a subset of smaller order type is
      -- countably colorable
      (∀ (S : Set V),
        Ordinal.type (Subrel (· < ·) S) <
          Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) →
        Nonempty ((G.induce S).Coloring ℕ)) :=
  sorry

/--
Erdős Problem #919, Part 2 [Er69b]:

What if instead we ask for G to have chromatic number ℵ₁?

Is there a graph on a well-ordered set of order type ω₂ · ω₂ with chromatic
number exactly ℵ₁ such that every subgraph induced on a subset of strictly
smaller order type has chromatic number ≤ ℵ₀?
-/
theorem erdos_problem_919_part2 :
    ∃ (V : Type) (_ : LinearOrder V) (_ : IsWellOrder V (· < ·))
      (G : SimpleGraph V),
      -- The order type of V is ω₂ · ω₂
      Ordinal.type ((· < ·) : V → V → Prop) =
        Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) ∧
      -- G has chromatic number exactly ℵ₁:
      -- any proper coloring needs ≥ ℵ₁ colors
      (∀ (α : Type), Nonempty (G.Coloring α) → aleph 1 ≤ #α) ∧
      -- and G is ℵ₁-colorable
      (∃ (α : Type), #α ≤ aleph 1 ∧ Nonempty (G.Coloring α)) ∧
      -- Every induced subgraph on a subset of smaller order type is
      -- countably colorable
      (∀ (S : Set V),
        Ordinal.type (Subrel (· < ·) S) <
          Cardinal.ord (aleph 2) * Cardinal.ord (aleph 2) →
        Nonempty ((G.induce S).Coloring ℕ)) :=
  sorry

end
