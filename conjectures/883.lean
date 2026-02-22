import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic

open Finset

/--
The coprimality graph on a subset A of natural numbers: two distinct elements
are connected by an edge if and only if they are coprime (gcd = 1).
-/
def coprimeGraph (A : Finset ℕ) : SimpleGraph ℕ where
  Adj x y := x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ Nat.Coprime x y
  symm := by
    intro x y ⟨hx, hy, hne, hcop⟩
    exact ⟨hy, hx, hne.symm, hcop.symm⟩
  loopless := ⟨fun x ⟨_, _, hne, _⟩ => hne rfl⟩

/--
A graph contains a cycle of length k: there exist k distinct vertices
v₀, ..., v_{k-1} such that v_i is adjacent to v_{(i+1) mod k} for all i.
Uses ZMod k for natural cyclic indexing. For k < 3 this is vacuously false
due to the loopless/irreflexive properties of simple graphs.
-/
def SimpleGraph.ContainsCycle {α : Type*} (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ f : ZMod k → α, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1))

/--
The threshold function: ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋, equal to the count of
integers in {1, ..., n} divisible by 2 or 3 (by inclusion-exclusion).
-/
def erdos883Threshold (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/--
Erdős Problem #883 (open):
For A ⊆ {1, ..., n}, let G(A) be the coprimality graph on A. If
|A| > ⌊n/2⌋ + ⌊n/3⌋ - ⌊n/6⌋ then G(A) contains all odd cycles
of length at most n/3 + 1.

A problem of Erdős and Sárkőzy [ErSa97], who proved this for cycles of
length ≤ cn for some constant c > 0. The threshold is best possible since
the set of integers in {1,...,n} divisible by 2 or 3 has this cardinality
and its coprimality graph contains no triangles.
-/
theorem erdos_problem_883_conjecture :
    ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) →
      A.card > erdos883Threshold n →
      ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ n / 3 + 1 →
        (coprimeGraph A).ContainsCycle k :=
  sorry
