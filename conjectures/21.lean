import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

/--
A family F of n-element subsets of ℕ is intersecting if every two members
of F have non-empty intersection.
-/
def IsIntersectingNFamily (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  (∀ A ∈ F, A.card = n) ∧ (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)

/--
A family F of n-sets covers all small sets if every set S with |S| ≤ n - 1
is disjoint from at least one member of F.
-/
def CoversAllSmallSets (F : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/--
f(n) is the minimal size of an intersecting family of n-sets that covers
all sets of size at most n - 1.
-/
noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ F : Finset (Finset ℕ),
    F.card = k ∧ IsIntersectingNFamily F n ∧ CoversAllSmallSets F n}

/--
Erdős Problem #21 (proved by Kahn [Ka94]):
Let f(n) be the minimal size of an intersecting family F of n-element sets such
that any set S with |S| ≤ n - 1 is disjoint from at least one A ∈ F.
Then f(n) ≪ n, i.e., there exist constants C > 0 and N₀ such that
f(n) ≤ C · n for all n ≥ N₀.

Erdős and Lovász [ErLo75] proved (8/3)n - 3 ≤ f(n) ≪ n^{3/2} log n.
Kahn [Ka92b] improved the upper bound to f(n) ≪ n log n.
Kahn [Ka94] proved the upper bound f(n) ≪ n, settling the conjecture.
-/
theorem erdos_problem_21 :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (erdosLovaszF n : ℝ) ≤ C * n :=
  sorry
