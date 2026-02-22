import Mathlib.Combinatorics.SimpleGraph.Init
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #752

Let $G$ be a graph with minimum degree $k$ and girth $>2s$ (i.e. $G$ contains
no cycles of length $\leq 2s$). Must there be $\gg k^s$ many distinct cycle
lengths in $G$?

A question of Erdős, Faudree, and Schelp, who proved it when $s=2$.

The answer is yes, proved by Sudakov and Verstraëte [SuVe08], who in fact
proved that under the assumption of average degree $k$ and girth $>2s$ there
are at least $\gg k^s$ many consecutive even integers which are cycle lengths
in $G$.

https://www.erdosproblems.com/752

Tags: graph theory, cycles
-/

/-- The set of cycle lengths occurring in a simple graph. -/
def cycleLengths752 {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n | ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Sudakov–Verstraëte Theorem (Erdős Problem #752)**:

There exists an absolute constant $c > 0$ such that for every finite graph $G$
with minimum degree at least $k$ and girth greater than $2s$, the number of
distinct cycle lengths in $G$ is at least $c \cdot k^s$.
-/
theorem erdos_problem_752 :
    ∃ c : ℝ, c > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj]
      (k s : ℕ),
      (∀ v : V, k ≤ G.degree v) →
      (∀ (v : V) (p : G.Walk v v), p.IsCycle → 2 * s < p.length) →
      c * (k : ℝ) ^ s ≤ ((cycleLengths752 G).ncard : ℝ) :=
  sorry

end
