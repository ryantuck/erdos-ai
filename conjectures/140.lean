import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Real Filter

noncomputable section

/-- A finite set S ⊆ ℕ is 3-AP-free if it contains no non-trivial 3-term
    arithmetic progression: for all a, b, c ∈ S satisfying a + c = 2 * b,
    we have a = b (which forces a = b = c, i.e., the progression is trivial). -/
def IsThreeAPFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a + c = 2 * b → a = b

/-- r₃(N) is the maximum size of a 3-AP-free subset of {1, ..., N}. -/
noncomputable def r3 (N : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset ℕ,
    (∀ x ∈ S, 1 ≤ x ∧ x ≤ N) ∧
    IsThreeAPFree S ∧
    S.card = k }

/--
Erdős Problem #140 [ErGr80, Er81, Er97c]:
Let r₃(N) be the size of the largest subset of {1, ..., N} containing no
non-trivial 3-term arithmetic progression. Then r₃(N) ≪ N / (log N)^C
for every C > 0.

Formally: for every C > 0 there exists a constant K > 0 such that
  r₃(N) ≤ K * N / (log N)^C  for all sufficiently large N.

Proved by Kelley and Meka [KeMe23].
-/
theorem erdos_problem_140 :
    ∀ C : ℝ, 0 < C →
    ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in atTop,
      (r3 N : ℝ) ≤ K * (N : ℝ) / (Real.log (N : ℝ)) ^ C :=
  sorry

end
