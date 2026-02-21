import Mathlib.Data.Nat.Totient
import Mathlib.Logic.Equiv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Real Classical

noncomputable section

/-!
# Erdős Problem #415

For any n let F(n) be the largest k such that every one of the k! possible
ordering patterns appears in some consecutive sequence φ(m+1), ..., φ(m+k)
with m + k ≤ n.

Conjecture 1: F(n) = (c + o(1)) log log log n for some constant c.
Conjecture 2: The first pattern to fail is always the strictly decreasing one:
  φ(m+1) > φ(m+2) > ⋯ > φ(m+k).
Conjecture 3: The "natural" ordering (mimicking φ(1), ..., φ(k)) is the most
  likely to appear.

Erdős [Er36b] proved that F(n) ≍ log log log n, and similarly for σ, τ, ν,
or any decent additive or multiplicative function.
-/

/-- A block φ(m+1), ..., φ(m+k) exhibits ordering pattern σ ∈ Sₖ if σ sorts
    the totient values into increasing order: for all i < j in Fin k,
    φ(m + 1 + σ(i)) < φ(m + 1 + σ(j)). -/
def erdos415_exhibitsPattern (k m : ℕ) (σ : Equiv.Perm (Fin k)) : Prop :=
  ∀ i j : Fin k, i < j →
    Nat.totient (m + 1 + (σ i).val) < Nat.totient (m + 1 + (σ j).val)

/-- F(n) is the largest k such that every permutation pattern of length k is
    realized among consecutive totient values up to n. -/
noncomputable def erdos415_F (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ σ : Equiv.Perm (Fin k),
    ∃ m : ℕ, m + k ≤ n ∧ erdos415_exhibitsPattern k m σ}

/-- The descending permutation of Fin k: i ↦ k - 1 - i (reversal). -/
def erdos415_descendingPerm (k : ℕ) : Equiv.Perm (Fin k) where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv i := Fin.rev_rev i
  right_inv i := Fin.rev_rev i

/-- Number of starting positions m (with m + k ≤ n) where the block of length k
    exhibits pattern σ. -/
noncomputable def erdos415_patternCount (k n : ℕ) (σ : Equiv.Perm (Fin k)) : ℕ :=
  ((Finset.range n).filter (fun m => m + k ≤ n ∧ erdos415_exhibitsPattern k m σ)).card

/-- The "natural" ordering pattern of length k: the sorting permutation of
    (φ(1), φ(2), ..., φ(k)) with ties broken by position. -/
noncomputable def erdos415_naturalPattern (k : ℕ) : Equiv.Perm (Fin k) := by
  exact sorry

/--
Erdős Problem #415, Part 1 [ErGr80, p.82]:

F(n) / log(log(log(n))) → c as n → ∞ for some positive constant c.
-/
theorem erdos_problem_415_part1 :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ =>
        (erdos415_F n : ℝ) / Real.log (Real.log (Real.log (n : ℝ))))
        atTop (nhds c) :=
  sorry

/--
Erdős Problem #415, Part 2 [ErGr80, p.82]:

The first ordering pattern to fail is always the strictly decreasing one.
If the descending pattern of length k appears in totient blocks up to n,
then so does every pattern of length k.
-/
theorem erdos_problem_415_part2 :
    ∀ n k : ℕ,
      (∃ m : ℕ, m + k ≤ n ∧ erdos415_exhibitsPattern k m (erdos415_descendingPerm k)) →
        ∀ σ : Equiv.Perm (Fin k),
          ∃ m : ℕ, m + k ≤ n ∧ erdos415_exhibitsPattern k m σ :=
  sorry

/--
Erdős Problem #415, Part 3 [ErGr80, p.82]:

The "natural" ordering pattern (mimicking φ(1), ..., φ(k)) is the most likely.
For any pattern σ, the count of blocks exhibiting σ is eventually at most the
count exhibiting the natural pattern.
-/
theorem erdos_problem_415_part3 (k : ℕ) (hk : 1 ≤ k) :
    ∀ σ : Equiv.Perm (Fin k),
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        erdos415_patternCount k n σ ≤ erdos415_patternCount k n (erdos415_naturalPattern k) :=
  sorry

end
