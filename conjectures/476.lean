import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

open Finset

/--
The restricted sumset A +̂ A = {a + b : a, b ∈ A, a ≠ b}, consisting of all
pairwise sums of distinct elements from A.
-/
def restrictedSumset476 {p : ℕ} (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.biUnion (fun a => (A.erase a).image (fun b => a + b))

/--
Erdős-Heilbronn Conjecture (Problem #476):

Let p be a prime and let A ⊆ 𝔽_p. Define the restricted sumset
  A +̂ A = {a + b : a, b ∈ A, a ≠ b}.
Is it true that |A +̂ A| ≥ min(2|A| - 3, p)?

A question of Erdős and Heilbronn. Solved in the affirmative by
da Silva and Hamidoune [dSHa94].
-/
theorem erdos_problem_476 (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)) :
    (restrictedSumset476 A).card ≥ min (2 * A.card - 3) p :=
  sorry
