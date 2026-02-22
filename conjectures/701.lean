import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

/-- A family of finite sets is downward closed (an abstract simplicial complex)
    if whenever A is in the family and B ⊆ A, then B is also in the family. -/
def IsDownwardClosed {α : Type*} [DecidableEq α] (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B : Finset α, B ⊆ A → B ∈ F

/-- A family of finite sets is intersecting if every two members have
    nonempty intersection. -/
def IsIntersectingFamily {α : Type*} [DecidableEq α] (F' : Finset (Finset α)) : Prop :=
  ∀ A ∈ F', ∀ B ∈ F', (A ∩ B).Nonempty

/--
Erdős Problem #701 (Chvátal's Conjecture):

Let F be a family of finite sets closed under taking subsets (i.e. if B ⊆ A ∈ F
then B ∈ F). There exists some element x such that whenever F' ⊆ F is an
intersecting subfamily we have |F'| ≤ |{A ∈ F : x ∈ A}|.

Equivalently, the maximum intersecting subfamily of a downward-closed family
has size at most the maximum degree.
-/
theorem erdos_problem_701 {α : Type*} [DecidableEq α] [Nonempty α]
    (F : Finset (Finset α))
    (hF : IsDownwardClosed F) :
    ∃ x : α, ∀ F' : Finset (Finset α), F' ⊆ F → IsIntersectingFamily F' →
      F'.card ≤ (F.filter (fun A => x ∈ A)).card :=
  sorry
