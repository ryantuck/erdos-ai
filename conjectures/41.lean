import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open scoped Classical
open Filter

/--
A set A ⊆ ℕ is a **B₃ set** if all triple sums are distinct aside from
trivial coincidences: for a ≤ b ≤ c and d ≤ e ≤ f, all in A,
a + b + c = d + e + f implies a = d, b = e, c = f.
-/
def IsB3Set (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, ∀ e ∈ A, ∀ f ∈ A,
    a + b + c = d + e + f → a ≤ b → b ≤ c → d ≤ e → e ≤ f →
      a = d ∧ b = e ∧ c = f

/--
The counting function for A up to N: |A ∩ {1, …, N}|.
-/
noncomputable def countingFn41 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #41 [Er77c, ErGr80, Er81, Er85c, Er91, Er95, Er97c]:

Let A ⊂ ℕ be an infinite B₃ set (all triple sums a + b + c are distinct
aside from trivial coincidences). Is it true that
  lim inf |A ∩ {1, …, N}| / N^{1/3} = 0 ?

Erdős proved the analogous result for B₂ sets (Sidon sets): every infinite
Sidon set satisfies lim inf |A ∩ {1,…,N}| / N^{1/2} = 0. The general
conjecture for Bₕ sets (h-fold sums distinct) states that
lim inf |A ∩ {1,…,N}| / N^{1/h} = 0. This was proved for h = 4 by Nash
and for all even h by Chen.
-/
theorem erdos_problem_41 (A : Set ℕ) (hA : A.Infinite) (hB3 : IsB3Set A) :
    liminf (fun N => (countingFn41 A N : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3)) atTop = 0 :=
  sorry
