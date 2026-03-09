import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open SimpleGraph

/--
A simple graph contains a 4-cycle (C₄) if there exist four distinct vertices
a, b, c, d such that a~b, b~c, c~d, d~a.
-/
def SimpleGraph.ContainsCycle4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d : V), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/--
Every simple graph on n vertices with minimum degree ≥ d contains a C₄.
-/
def ForcesCycle4 (n d : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, d ≤ G.degree v) → G.ContainsCycle4

/--
f(n) is the minimal d such that every graph on n vertices with minimum
degree ≥ d must contain a C₄.
-/
noncomputable def minDegreeForCycle4 (n : ℕ) : ℕ :=
  sInf {d : ℕ | ForcesCycle4 n d}

/--
Erdős Problem #85 [Er93,p.345] [Er94b] [Er95] [Er96]:

Let n ≥ 4 and f(n) be minimal such that every graph on n vertices with
minimum degree ≥ f(n) contains a C₄. Is it true that, for all large n,
f(n+1) ≥ f(n)?

The function f(n) is related to the Ramsey number R(C₄, K_{1,n}).
It is known that f(n) = (1 + o(1))√n and f(4) = 2.
-/
theorem erdos_problem_85 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      minDegreeForCycle4 (n + 1) ≥ minDegreeForCycle4 n :=
  sorry
