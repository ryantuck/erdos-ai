import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card

open Cardinal Set

noncomputable section

/-!
# Erdős Problem #602

Let $(A_i)$ be a family of sets with $|A_i| = \aleph_0$ for all $i$, such that
for any $i \neq j$ we have $|A_i \cap A_j|$ finite and $\neq 1$. Is there a
2-colouring of $\bigcup A_i$ such that no $A_i$ is monochromatic?

A problem of Komjáth [Er87]. The existence of such a 2-colouring is sometimes
known as Property B.

Tags: combinatorics, set theory
-/

/-- Property B for a family of sets: there exists a 2-colouring of the union
    such that no set in the family is monochromatic (both colours appear). -/
def HasPropertyB {α : Type*} {ι : Type*} (A : ι → Set α) : Prop :=
  ∃ c : α → Bool, ∀ i : ι, (∃ x ∈ A i, c x = true) ∧ (∃ x ∈ A i, c x = false)

/--
Erdős Problem #602 [Er87]:

Let $(A_i)$ be a family of sets with $|A_i| = \aleph_0$ for all $i$, such that
for any $i \neq j$, $|A_i \cap A_j|$ is finite and $\neq 1$. Then the family
has Property B: there is a 2-colouring of $\bigcup A_i$ such that no $A_i$ is
monochromatic.
-/
theorem erdos_problem_602 {α : Type*} {ι : Type*} (A : ι → Set α)
    (hcount : ∀ i, #(↥(A i)) = ℵ₀)
    (hfin : ∀ i j, i ≠ j → (A i ∩ A j).Finite)
    (hne1 : ∀ i j, i ≠ j → (A i ∩ A j).ncard ≠ 1) :
    HasPropertyB A :=
  sorry

end
