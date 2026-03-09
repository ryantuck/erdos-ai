import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

open Finset

/--
A finite set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are
distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have
{a, b} = {c, d}.
-/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
The sumset A + A of a finite set A ⊆ ℕ.
-/
def sumset (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/--
An element n is **isolated** in a set S ⊆ ℕ if neither n - 1 nor n + 1
belongs to S.
-/
def isIsolatedIn (n : ℕ) (S : Finset ℕ) : Bool :=
  (n + 1 ∉ S) && (n = 0 || n - 1 ∉ S)

/--
Erdős Problem #152 [ESS94]:

For any M ≥ 1, if A ⊆ ℕ is a sufficiently large finite Sidon set then there
are at least M elements a ∈ A + A such that a + 1 ∉ A + A and a - 1 ∉ A + A
(i.e., at least M isolated points in the sumset).
-/
theorem erdos_problem_152 :
    ∀ M : ℕ, ∃ N : ℕ, ∀ (A : Finset ℕ),
      IsSidonSet A →
      N ≤ A.card →
      M ≤ ((sumset A).filter (fun a => isIsolatedIn a (sumset A))).card :=
  sorry
