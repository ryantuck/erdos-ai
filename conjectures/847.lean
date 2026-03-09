import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

open Finset Set

/--
A set S ⊆ ℕ is **3-AP-free** if it contains no three-term arithmetic
progression, i.e., there are no a, d with d > 0 such that a, a+d, a+2d ∈ S.
-/
def ThreeAPFree (S : Set ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → a ∈ S → a + d ∈ S → a + 2 * d ∉ S

/--
A set A ⊆ ℕ is **ε-AP-free-dense** if every finite subset B ⊆ A of size n
contains a subset of size ≥ εn which is 3-AP-free.
-/
def EpsAPFreeDense (A : Set ℕ) (ε : ℝ) : Prop :=
  ∀ B : Finset ℕ,
    (↑B : Set ℕ) ⊆ A →
    ∃ C : Finset ℕ,
      (↑C : Set ℕ) ⊆ ↑B ∧
      ε * B.card ≤ C.card ∧
      ThreeAPFree (↑C : Set ℕ)

/--
A set A ⊆ ℕ is **finitely 3-AP-free-colourable** if it is the union of
finitely many 3-AP-free sets.
-/
def FinitelyAPFreeColourable (A : Set ℕ) : Prop :=
  ∃ (k : ℕ) (F : Fin k → Set ℕ),
    (∀ i, ThreeAPFree (F i)) ∧
    A ⊆ ⋃ i, F i

/--
Erdős Problem #847 \[Er92b\]:

Let A ⊂ ℕ be an infinite set for which there exists some ε > 0 such that in
any subset of A of size n there is a subset of size at least εn which contains
no three-term arithmetic progression.

Is it true that A is the union of a finite number of sets which contain no
three-term arithmetic progression?

A problem of Erdős, Nešetřil, and Rödl. The answer is **no** (disproved by
Reiher, Rödl, and Sales).
-/
theorem erdos_problem_847 :
    ¬(∀ (A : Set ℕ),
      A.Infinite →
      (∃ ε : ℝ, 0 < ε ∧ EpsAPFreeDense A ε) →
      FinitelyAPFreeColourable A) :=
  sorry
