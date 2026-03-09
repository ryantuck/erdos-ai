import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic

open Filter Topology Real Classical

noncomputable section

/--
The sequence of squarefree numbers in increasing order, indexed starting at 0.
-/
def squarefreeSeq : ℕ → ℕ := sorry

/--
`squarefreeSeq` enumerates exactly the squarefree numbers in increasing order.
-/
axiom squarefreeSeq_strictMono : StrictMono squarefreeSeq
axiom squarefreeSeq_squarefree (n : ℕ) : Squarefree (squarefreeSeq n)
axiom squarefreeSeq_surj (m : ℕ) (hm : Squarefree m) : ∃ n, squarefreeSeq n = m

/--
Erdős Problem #208, Part 1 [Er51, Er61, Er65b, Er79, Er81h]:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that for
any ε > 0 and all sufficiently large n,
  s_{n+1} - s_n ≪_ε s_n^ε ?

That is, for every ε > 0 there exist constants C > 0 and N₀ such that for all
n ≥ N₀, s_{n+1} - s_n ≤ C · s_n^ε.
-/
theorem erdos_problem_208a (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        C * (squarefreeSeq n : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #208, Part 2 [Er51, Er61, Er65b, Er79, Er81h]:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that
  s_{n+1} - s_n ≤ (1 + o(1)) · (π²/6) · (log s_n / log log s_n) ?

Erdős showed this bound would be best possible, as there are infinitely many n
achieving the reverse inequality.
-/
theorem erdos_problem_208b :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        (1 + δ) * (π ^ 2 / 6) *
          (Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))) :=
  sorry

end
