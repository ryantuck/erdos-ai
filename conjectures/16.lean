import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open Set Filter

/--
The set of numbers of the form 2^k + p where p is prime and k >= 1.
Note: The problem statement usually implies powers of 2.
We assume k can be any natural number, but since we restrict to odd integers,
and p=2 is the only even prime, 2^k + 2 is even for k >= 1.
If k=0, 1+p.
The problem likely refers to "powers of 2" as 1, 2, 4, ...
Let's just use `∃ k p, Nat.Prime p ∧ n = 2^k + p`.
-/
def is_of_form (n : ℕ) : Prop :=
  ∃ k p, Nat.Prime p ∧ n = 2^k + p

/--
S is the set of odd integers not of the form 2^k + p.
-/
def S : Set ℕ := { n | Odd n ∧ ¬ is_of_form n }

/--
Definition of an infinite arithmetic progression of natural numbers.
P = { a + k*d | k ∈ ℕ } for some a, d with d > 0.
-/
def IsInfiniteAP (P : Set ℕ) : Prop :=
  ∃ a d, d > 0 ∧ P = { n | ∃ k, n = a + k * d }

/--
The upper density of a set of natural numbers.
-/
noncomputable def upperDensity (s : Set ℕ) : ℝ :=
  limsup (fun n => ((s ∩ {i | i < n}).ncard : ℝ) / n) atTop

/--
Erdős's conjecture (Problem #16):
The set of odd integers not of the form 2^k + p is the union of an infinite
arithmetic progression and a set of density 0.
-/
theorem erdos_problem_16_conjecture :
  ∃ P Z : Set ℕ, IsInfiniteAP P ∧ upperDensity Z = 0 ∧ S = P ∪ Z :=
sorry
