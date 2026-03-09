import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Nat

noncomputable section

/--
An odd natural number n is "representable" if it can be written as p + 2^k + 2^l
where p is prime and k, l ≥ 0.
-/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ p k l : ℕ, Nat.Prime p ∧ n = p + 2 ^ k + 2 ^ l

/--
The set A of all odd integers ≥ 1 that are NOT of the form p + 2^k + 2^l.
-/
def erdos9Set : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ ¬Even n ∧ ¬IsRepresentable n}

/--
The counting function for a set S ⊆ ℕ: the number of elements in S ∩ {0, ..., N}.
-/
noncomputable def countingFunction (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic N)

/--
The upper density of a set S ⊆ ℕ:
  lim sup_{N → ∞} |S ∩ {0, ..., N}| / (N + 1)
-/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countingFunction S N : ℝ) / (N + 1 : ℝ)) Filter.atTop

/--
Erdős Problem #9 [Er77c, ErGr80, Er85c, Er92c, Er95, Er97, Er97c, Er97e]:

Let A be the set of all odd integers ≥ 1 not of the form p + 2^k + 2^l
(where k, l ≥ 0 and p is prime). Is the upper density of A positive?
-/
theorem erdos_problem_9 : upperDensity erdos9Set > 0 :=
  sorry

end
