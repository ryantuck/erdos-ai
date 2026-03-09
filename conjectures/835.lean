import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

open Finset

/--
Erdős Problem #835 [Er74d,p.283]:

Does there exist a k > 2 such that the k-sized subsets of {1,…,2k} can be
coloured with k+1 colours such that for every (k+1)-element subset A of
{1,…,2k}, all k+1 colours appear among the k-sized subsets of A?

A problem of Erdős and Rosenfeld. This is trivially possible for k = 2.
This is equivalent to asking whether the chromatic number of the Johnson
graph J(2k,k) equals k+1 for some k > 2.
-/
theorem erdos_problem_835 :
    ∃ k : ℕ, k > 2 ∧
      ∃ c : Finset (Fin (2 * k)) → Fin (k + 1),
        (∀ A ∈ (Finset.univ : Finset (Fin (2 * k))).powerset.filter (fun s => s.card = k + 1),
          ∀ color : Fin (k + 1),
            ∃ S ∈ A.powerset.filter (fun s => s.card = k),
              c S = color) :=
  sorry
