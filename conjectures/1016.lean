import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #1016

Let h(n) be minimal such that there is a graph on n vertices with n + h(n)
edges which contains a cycle on k vertices, for all 3 ≤ k ≤ n. Such graphs
are called pancyclic. Estimate h(n). In particular, is it true that
  h(n) ≥ log₂ n + log* n - O(1),
where log* n is the iterated logarithmic function?

A problem of Bondy [Bo71], who claimed a proof (without details) of
  log₂(n−1) − 1 ≤ h(n) ≤ log₂ n + log* n + O(1).
Erdős [Er71] believed the upper bound is closer to the truth.
-/

/-- A simple graph on `Fin n` contains a cycle of length `k` (for `k ≥ 3`)
    if there is an injective map from `Fin k` into the vertices such that
    consecutive vertices in the cycle map to adjacent vertices. -/
def ContainsCycle {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (hk : k ≥ 3) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    ∀ i : Fin k, G.Adj (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩)

/-- A graph on `Fin n` is pancyclic if it contains cycles of every length
    from 3 to n. -/
def IsPancyclic {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ k (hk : k ≥ 3), k ≤ n → ContainsCycle G k hk

/-- The number of edges of a simple graph on `Fin n`, counted as the number
    of pairs (i, j) with i < j that are adjacent. -/
noncomputable def numEdges {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).card

/-- The minimum excess edges h(n) for a pancyclic graph: the smallest h such
    that there exists a pancyclic graph on n vertices with n + h edges. -/
def pancyclicExcess (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∃ G : SimpleGraph (Fin n),
    numEdges G = n + h ∧ IsPancyclic G}

/-- Auxiliary definition for the iterated logarithm with explicit fuel. -/
def iteratedLog₂Aux : ℕ → ℕ → ℕ
  | _, 0 => 0
  | _, 1 => 0
  | 0, _ + 2 => 0
  | fuel + 1, n + 2 => 1 + iteratedLog₂Aux fuel (Nat.log 2 (n + 2))

/-- The iterated logarithm log*(n) (base 2). -/
def iteratedLog₂ (n : ℕ) : ℕ := iteratedLog₂Aux n n

/--
Erdős Problem #1016 [Er71]:

The minimum number of edges beyond n needed for a pancyclic graph on n
vertices satisfies h(n) ≥ ⌊log₂ n⌋ + log* n - O(1).

Formulated as: there exists a constant C such that for all n ≥ 3,
  h(n) + C ≥ ⌊log₂ n⌋ + log* n.
-/
theorem erdos_problem_1016 :
    ∃ C : ℕ, ∀ n, n ≥ 3 →
      pancyclicExcess n + C ≥ Nat.log 2 n + iteratedLog₂ n :=
  sorry

end
