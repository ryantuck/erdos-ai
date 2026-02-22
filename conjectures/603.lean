import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Set.Card

open Cardinal Set

noncomputable section

/-!
# Erdős Problem #603

Let $(A_i)$ be a family of countably infinite sets such that $|A_i \cap A_j| \neq 2$
for all $i \neq j$. Find the smallest cardinal $C$ such that $\bigcup A_i$ can always
be coloured with at most $C$ colours so that no $A_i$ is monochromatic.

A problem of Komjáth [Er87]. If instead we have $|A_i \cap A_j| \neq 1$ then
Komjáth showed that this is possible with at most $\aleph_0$ colours.

Tags: combinatorics, set theory
-/

/--
Erdős Problem #603 [Er87]:

Let $(A_i)$ be a family of countably infinite sets such that $|A_i \cap A_j| \neq 2$
for all $i \neq j$. Then there is a colouring with at most $\aleph_0$ colours so that
no $A_i$ is monochromatic.

This is conjectured by analogy with the Komjáth result for the $|A_i \cap A_j| \neq 1$
case, where $\aleph_0$ colours suffice.
-/
theorem erdos_problem_603 {α : Type*} {ι : Type*} (A : ι → Set α)
    (hcount : ∀ i, #(↥(A i)) = ℵ₀)
    (hne2 : ∀ i j, i ≠ j → (A i ∩ A j).ncard ≠ 2) :
    ∃ c : α → ℕ, ∀ i : ι, ∃ x ∈ A i, ∃ y ∈ A i, c x ≠ c y :=
  sorry

end
