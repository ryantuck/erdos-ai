import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open SimpleGraph Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #626

Let k ≥ 4 and g_k(n) denote the largest m such that there is a graph on n vertices
with chromatic number k and girth > m (i.e. contains no cycle of length ≤ m). Does
  lim_{n → ∞} g_k(n) / log n
exist?

Conversely, if h^{(m)}(n) is the maximal chromatic number of a graph on n vertices
with girth > m then does
  lim_{n → ∞} log h^{(m)}(n) / log n
exist, and what is its value?

It is known that
  (1 / (4 log k)) log n ≤ g_k(n) ≤ (2 / log(k-2)) log n + 1,
the lower bound due to Kostochka [Ko88] and the upper bound to Erdős [Er59b].

Erdős [Er59b] proved that
  lim_{n → ∞} log h^{(m)}(n) / log n ≫ 1/m
and, for odd m,
  lim_{n → ∞} log h^{(m)}(n) / log n ≤ 2/(m+1),
and conjectured this is sharp.

Tags: graph theory, chromatic number, cycles
-/

/-- The chromatic number of a simple graph on `Fin n`: the minimum number of colors `k`
    such that there exists a proper coloring `f : Fin n → Fin k`. -/
noncomputable def finChromaticNumber626 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∃ f : Fin n → Fin k, ∀ u v, G.Adj u v → f u ≠ f v}

/-- A graph on `Fin n` has girth greater than `m` if every cycle has length
    strictly greater than `m`. -/
def hasGirthGt626 {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : Prop :=
  ∀ v : Fin n, ∀ p : G.Walk v v, p.IsCycle → m < p.length

/-- `g626 k n` is the largest `m` such that there exists a graph on `n` vertices
    with chromatic number `k` and girth `> m`. Returns 0 if no such graph exists. -/
noncomputable def g626 (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n), finChromaticNumber626 G = k ∧ hasGirthGt626 G m}

/-- `h626 m n` is the maximal chromatic number of a graph on `n` vertices
    with girth `> m`. -/
noncomputable def h626 (m n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n), finChromaticNumber626 G = k ∧ hasGirthGt626 G m}

/--
**Erdős Problem #626, Part 1** [Er59b][Er62b][Er69b]:

For k ≥ 4, the limit lim_{n → ∞} g_k(n) / log n exists.
-/
theorem erdos_problem_626a (k : ℕ) (hk : k ≥ 4) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => (g626 k n : ℝ) / Real.log (n : ℝ))
      atTop (nhds L) :=
  sorry

/--
**Erdős Problem #626, Part 2** [Er59b][Er62b][Er69b]:

For m ≥ 1, the limit lim_{n → ∞} log h^{(m)}(n) / log n exists.
-/
theorem erdos_problem_626b (m : ℕ) (hm : m ≥ 1) :
    ∃ L : ℝ, Tendsto (fun n : ℕ => Real.log (h626 m n : ℝ) / Real.log (n : ℝ))
      atTop (nhds L) :=
  sorry

end
