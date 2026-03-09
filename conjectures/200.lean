import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Data.Set.Finite.Basic

open Filter Asymptotics Real

/--
A set S ⊆ ℕ is an arithmetic progression of length k if there exist a, d such that
S = {a, a+d, a+2d, ..., a+(k-1)d} with d > 0.
-/
def IsArithProgressionOfLength (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ S = Finset.image (fun i => a + d * i) (Finset.range k)

/--
The length of the longest arithmetic progression of primes in {1, ..., N}.
-/
noncomputable def longestPrimeAP (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, IsArithProgressionOfLength S k ∧
    (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, 1 ≤ p ∧ p ≤ N)}

/--
Erdős Problem #200 [ErGr79, ErGr80]:

Does the longest arithmetic progression of primes in {1, …, N} have length o(log N)?

It follows from the prime number theorem that such a progression has length
≤ (1 + o(1)) log N.
-/
theorem erdos_problem_200 :
    (fun N => (longestPrimeAP N : ℝ)) =o[atTop] (fun N => log (N : ℝ)) :=
  sorry
