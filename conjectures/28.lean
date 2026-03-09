import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Set Pointwise

/--
The representation function for a set A ⊆ ℕ, counting the number of ways
to write n as a + b with a, b ∈ A.
-/
noncomputable def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/--
Erdős Problem #28 [ErTu41, Er56, Er57, Er59, Er61, Er65, Er65b, Er69,
Er70c, Er73, Er77c, ErGr80, Er81, Er85c, Er89d, Er90, Er94b, Er95,
Er97c, Er97f]:

Conjectured by Erdős and Turán. If A ⊆ ℕ is such that A + A contains
all but finitely many natural numbers, then the representation function
1_A ∗ 1_A(n) is unbounded, i.e., for every M there exists n with
repFunction A n ≥ M.
-/
theorem erdos_problem_28 (A : Set ℕ)
    (h : {n : ℕ | n ∉ (A + A)}.Finite) :
    ∀ M : ℕ, ∃ n : ℕ, repFunction A n ≥ M :=
  sorry
