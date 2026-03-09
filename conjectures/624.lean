import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.Filter.AtTopBot.Basic

/--
For a given n, the minimum m such that there exists a function
f : Finset (Fin n) → Fin n with the property that for every Y ⊆ Fin n
with |Y| ≥ m, the image {f(A) : A ⊆ Y} covers all of Fin n.
-/
noncomputable def erdos624_H (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ f : Finset (Fin n) → Fin n,
    ∀ Y : Finset (Fin n), m ≤ Y.card →
      Finset.image f Y.powerset = Finset.univ}

/--
Erdős Problem #624:
Let X be a finite set of size n and H(n) be the minimum m such that there
exists f : P(X) → X so that for every Y ⊆ X with |Y| ≥ H(n) we have
{f(A) : A ⊆ Y} = X. Prove that H(n) - log₂ n → ∞.
-/
theorem erdos_problem_624 :
    Filter.Tendsto (fun n => (erdos624_H n : ℝ) - Real.logb 2 n)
      Filter.atTop Filter.atTop :=
  sorry
