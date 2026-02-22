import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1012

Let k ≥ 0. Let f(k) be the least integer such that every graph on n ≥ f(k)
vertices with at least C(n-k-1, 2) + C(k+2, 2) + 1 edges contains a cycle
of length n-k. Determine or estimate f(k).

Erdős [Er62e] proved that f(k) exists for all k ≥ 0.
Ore [Or61] proved f(0) = 1 (every graph on n ≥ 1 vertices with at least
C(n-1, 2) + 2 edges contains a Hamiltonian cycle).
Bondy [Bo71b] proved f(1) = 1.

Woodall [Wo72] proved that every graph on n ≥ 2k+3 vertices with at least
C(n-k-1, 2) + C(k+2, 2) + 1 edges contains a cycle of length l for all
3 ≤ l ≤ n-k. This settles the question completely with f(k) = 2k + 3.
-/

/-- A simple graph G contains a cycle of length m (m ≥ 3) if there exist m
    distinct vertices v₀, …, v_{m-1} such that v_i is adjacent to v_{(i+1) mod m}
    for all i. -/
def ContainsCycleOfLength1012 {V : Type*} (G : SimpleGraph V) (m : ℕ) (_ : m ≥ 3) : Prop :=
  ∃ (f : Fin m → V), Function.Injective f ∧
    ∀ i j : Fin m, j.val = (i.val + 1) % m → G.Adj (f i) (f j)

/--
Erdős Problem #1012 [Er62e] (solved by Woodall [Wo72]):

For every k ≥ 0 and n ≥ 2k + 3, every simple graph on n vertices with at least
C(n-k-1, 2) + C(k+2, 2) + 1 edges contains a cycle of length l for every
3 ≤ l ≤ n - k.

In particular, taking l = n - k, this answers Erdős' original question with
f(k) = 2k + 3.
-/
theorem erdos_problem_1012 (k n : ℕ) (hn : n ≥ 2 * k + 3)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ Nat.choose (n - k - 1) 2 + Nat.choose (k + 2) 2 + 1)
    (l : ℕ) (hl₁ : 3 ≤ l) (hl₂ : l ≤ n - k) :
    ContainsCycleOfLength1012 G l hl₁ :=
  sorry

end
