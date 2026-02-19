import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open Set Filter

/--
The set of numbers of the form p + 2^k + 2^l where p is prime and k, l >= 0.
-/
def is_of_form (n : ℕ) : Prop :=
  ∃ p k l, Nat.Prime p ∧ n = p + 2^k + 2^l

/--
A is the set of all odd integers >= 1 not of the form p + 2^k + 2^l.
Note: Odd n implies n >= 1 for n : Nat (since Odd 0 is false).
-/
def A : Set ℕ := { n | Odd n ∧ ¬ is_of_form n }

/--
The upper density of a set of natural numbers.
-/
noncomputable def upperDensity (s : Set ℕ) : ℝ :=
  limsup (fun n => ((s ∩ {i | i < n}).ncard : ℝ) / n) atTop

/--
Erdős's conjecture (Problem #9):
The upper density of the set of odd integers not of the form p + 2^k + 2^l is positive.
-/
theorem erdos_conjecture_9 : upperDensity A > 0 :=
sorry
