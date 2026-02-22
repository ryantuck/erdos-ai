import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Classical SimpleGraph Finset

/-!
# Erdős Problem #804

Let f(m,n) be maximal such that any graph on n vertices in which every induced
subgraph on m vertices has an independent set of size at least log n must
contain an independent set of size at least f(m,n).

Estimate f(n). In particular, is it true that f((log n)², n) ≥ n^{1/2 - o(1)}?
Is it true that f((log n)³, n) ≫ (log n)³?

A question of Erdős and Hajnal [Er91]. DISPROVED by Alon and Sudakov [AlSu07],
who proved that
  (log n)² / log(log n) ≪ f((log n)², n) ≪ (log n)²
and
  f((log n)³, n) ≍ (log n)² / log(log n).
-/

/-- An independent set in a simple graph: a finset of vertices with no edges
    between any two of its members. -/
def SimpleGraph.IsIndepSet {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

/-- The independence number of a graph on `Fin n`: the maximum cardinality of an
    independent set. -/
noncomputable def independenceNum {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ((univ : Finset (Fin n)).powerset.filter G.IsIndepSet).sup Finset.card

/-- `erdos804_f m n` is the largest `k` such that every graph on `n` vertices
    in which every induced subgraph on `m` vertices has an independent set of
    size `≥ ⌈log n⌉` must have independence number `≥ k`.

    Equivalently, the infimum of independence numbers over all qualifying
    graphs. -/
noncomputable def erdos804_f (m n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ G : SimpleGraph (Fin n),
    (∀ S : Finset (Fin n), S.card = m →
      ∃ T : Finset (Fin n), T ⊆ S ∧ T.card ≥ Nat.ceil (Real.log (n : ℝ)) ∧
        G.IsIndepSet T) ∧
    independenceNum G = k }

/--
Alon-Sudakov [AlSu07] upper bound: f((log n)², n) ≤ C · (log n)²
for some constant C > 0 and all sufficiently large n.

This disproves the conjecture of Erdős and Hajnal that
f((log n)², n) ≥ n^{1/2 - o(1)}.
-/
theorem erdos_804_part1_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 2)) n : ℝ) ≤
        C * (Real.log (n : ℝ)) ^ 2 :=
  sorry

/--
Alon-Sudakov [AlSu07] lower bound: f((log n)², n) ≥ c · (log n)² / log(log n)
for some constant c > 0 and all sufficiently large n.
-/
theorem erdos_804_part1_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 2)) n : ℝ) ≥
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) :=
  sorry

/--
Alon-Sudakov [AlSu07] upper bound: f((log n)³, n) ≤ C · (log n)² / log(log n)
for some constant C > 0 and all sufficiently large n.

This disproves the conjecture of Erdős and Hajnal that
f((log n)³, n) ≫ (log n)³.
-/
theorem erdos_804_part2_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 3)) n : ℝ) ≤
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) :=
  sorry

/--
Alon-Sudakov [AlSu07] lower bound: f((log n)³, n) ≥ c · (log n)² / log(log n)
for some constant c > 0 and all sufficiently large n.
-/
theorem erdos_804_part2_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos804_f (Nat.floor ((Real.log (n : ℝ)) ^ 3)) n : ℝ) ≥
        C * (Real.log (n : ℝ)) ^ 2 / Real.log (Real.log (n : ℝ)) :=
  sorry

end
