import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

open Finset

/-- A finite set of natural numbers is a Sidon set if all pairwise sums are
    distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have {a,b} = {c,d}. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A set S ⊆ ZMod n is a perfect difference set if every nonzero element of
    ZMod n can be represented as a difference s₁ - s₂ with s₁, s₂ ∈ S in
    exactly one way. -/
def IsPerfectDifferenceSet (n : ℕ) (S : Finset (ZMod n)) : Prop :=
  ∀ d : ZMod n, d ≠ 0 →
    ∃! p : ZMod n × ZMod n, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 - p.2 = d

/--
Erdős Problem #707 [Er76b, Er77c, Er79g, Er80, ErGr80, Er81, Er84b, Er84d,
Er85c, Er91, ErFr91, Er94c, Er97c]:

Let A ⊂ ℕ be a finite Sidon set. Is there some set B with A ⊆ B which is a
perfect difference set modulo p² + p + 1 for some prime p?

DISPROVED by Alexeev and Mixon [AlMi25], who showed that {1,2,4,8} cannot be
extended to a perfect difference set modulo p² + p + 1 for any prime p.
Hall [Ha47] had earlier shown that {1,3,9,10,13} cannot be extended to any
perfect difference set.

See also [44] and [329].
-/
theorem erdos_problem_707 :
    ∀ (A : Finset ℕ), IsSidonSet A →
      ∃ (p : ℕ), Nat.Prime p ∧
        ∃ (S : Finset (ZMod (p ^ 2 + p + 1))),
          IsPerfectDifferenceSet (p ^ 2 + p + 1) S ∧
            ∀ a ∈ A, (↑a : ZMod (p ^ 2 + p + 1)) ∈ S :=
  sorry
