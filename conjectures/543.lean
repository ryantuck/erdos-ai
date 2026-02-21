import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Defs

open Finset BigOperators Filter Classical

noncomputable section

/-- A subset A of an additive commutative group is subset-sum complete if every
    element of the group can be expressed as a sum over some subset of A. -/
def SubsetSumComplete {G : Type*} [AddCommGroup G]
    (A : Finset G) : Prop :=
  ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ ∑ x ∈ S, x = g

/-- The number of k-element subsets of ZMod n that are subset-sum complete.
    Returns 0 when n = 0 (since ZMod 0 = ℤ is not finite). -/
noncomputable def sscCountMod (n k : ℕ) : ℕ :=
  if h : n = 0 then 0
  else by
    haveI : NeZero n := ⟨h⟩
    exact ((Finset.univ : Finset (ZMod n)).powersetCard k).filter
      (fun A => SubsetSumComplete A) |>.card

/-- The total number of k-element subsets of ZMod n.
    Returns 0 when n = 0. -/
noncomputable def totalSubsetsMod (n k : ℕ) : ℕ :=
  if h : n = 0 then 0
  else by
    haveI : NeZero n := ⟨h⟩
    exact ((Finset.univ : Finset (ZMod n)).powersetCard k).card

/--
Erdős Problem #543 (disproved):

Define f(N) as the minimal k such that for every abelian group G of size N,
a uniformly random subset A ⊆ G of size k is subset-sum complete with
probability ≥ 1/2. Erdős and Rényi proved f(N) ≤ log₂ N + O(log log N).

The conjecture asked whether f(N) ≤ log₂ N + o(log log N). Erdős believed
this improvement is impossible [Er73,p.127], [ErHa78b].

This was confirmed (conjecture disproved) by ChatGPT and Tang. The
formalization states: no function g = o(log log N) can improve the bound,
even for cyclic groups ZMod N.
-/
theorem erdos_problem_543 :
    ¬ ∃ g : ℕ → ℝ,
      Tendsto (fun N => g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0) ∧
      ∀ᶠ (N : ℕ) in atTop,
        let k := Nat.ceil (Real.log (↑N : ℝ) / Real.log 2 + g N)
        2 * sscCountMod N k ≥ totalSubsetsMod N k :=
  sorry

end
