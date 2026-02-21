import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

/--
An *Egyptian fraction representation* of a/b is a nonempty finset S of positive
integers such that ∑_{n ∈ S} 1/n = a/b. Distinctness of denominators is
automatic from the finset structure.
-/
def IsEgyptianRepr (a b : ℕ) (S : Finset ℕ) : Prop :=
  S.Nonempty ∧ (∀ n ∈ S, 0 < n) ∧
  ∑ n ∈ S, (1 : ℝ) / (n : ℝ) = (a : ℝ) / (b : ℝ)

/--
Erdős Problem #305 [ErGr80, p.38]:

For integers 1 ≤ a < b, let D(a,b) be the minimal value of the largest
denominator n_k in an Egyptian fraction representation
a/b = 1/n₁ + ⋯ + 1/n_k with 1 ≤ n₁ < ⋯ < n_k.

Define D(b) = max_{1 ≤ a < b} D(a,b).

Is it true that D(b) ≪ b(log b)^{1+o(1)}?

Bleicher and Erdős [BlEr76] showed D(b) ≪ b(log b)².
This was proved by Yokota [Yo88] who showed
D(b) ≪ b(log b)(log log b)⁴(log log log b)²,
and improved by Liu and Sawhney [LiSa24] to
D(b) ≪ b(log b)(log log b)³(log log log b)^{O(1)}.

We formalize: for every ε > 0, there exist C > 0 and b₀ such that
for all b ≥ b₀ and all 1 ≤ a < b, there exists an Egyptian fraction
representation of a/b whose largest denominator is at most C · b · (log b)^{1+ε}.
-/
theorem erdos_problem_305 :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
      ∃ b₀ : ℕ, ∀ b : ℕ, b₀ ≤ b →
        ∀ a : ℕ, 1 ≤ a → a < b →
          ∃ S : Finset ℕ, IsEgyptianRepr a b S ∧
            ∀ n ∈ S, (n : ℝ) ≤ C * (b : ℝ) * (Real.log (b : ℝ)) ^ ((1 : ℝ) + ε) :=
  sorry
