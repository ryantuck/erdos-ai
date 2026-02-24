import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Real Filter

/-!
# Erdős Problem #18

We call m practical if every integer 1 ≤ n < m is the sum of distinct divisors
of m. If m is practical then let h(m) be such that h(m) many divisors always
suffice (i.e., h(m) is the least k such that every 1 ≤ n < m is the sum of at
most k distinct divisors of m).

Three questions:
1. Are there infinitely many practical m such that h(m) < (log log m)^O(1)?
2. Is it true that h(n!) < n^o(1)?
3. Or perhaps even h(n!) < (log n)^O(1)?

Known: Erdős showed h(n!) < n. Vose [Vo85] proved infinitely many practical m
with h(m) ≪ (log m)^(1/2). Erdős offered $250 for a proof or disproof of
whether h(n!) < (log n)^O(1).
-/

/-- m is practical if every integer 1 ≤ n < m can be represented as a sum
    of distinct divisors of m. -/
def IsPractical (m : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.sum id = n

/-- For a practical number m, practicalH m is the minimum k such that every
    integer 1 ≤ n < m can be expressed as the sum of at most k distinct
    divisors of m. -/
noncomputable def practicalH (m : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ n : ℕ, 1 ≤ n → n < m →
    ∃ S : Finset ℕ, S ⊆ Nat.divisors m ∧ S.card ≤ k ∧ S.sum id = n}

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h, Er95, Er96b, Er98]:

Conjecture (1): There are infinitely many practical m such that
h(m) < (log log m)^O(1), i.e., there exists a constant C > 0 such that
infinitely many practical m satisfy h(m) < (log log m)^C.
-/
theorem erdos_problem_18a :
    ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ m : ℕ, m ≥ N ∧ IsPractical m ∧
      (practicalH m : ℝ) < (Real.log (Real.log (m : ℝ))) ^ C :=
  sorry

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h, Er95, Er96b, Er98]:

Conjecture (2): h(n!) < n^o(1), i.e., for every ε > 0, for all
sufficiently large n, h(n!) < n^ε.
-/
theorem erdos_problem_18b :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (n : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #18 [Er74b, Er79, ErGr80, Er81h, Er95, Er96b, Er98]:

Conjecture (3): h(n!) < (log n)^O(1), i.e., there exists a constant C > 0
such that for all sufficiently large n, h(n!) < (log n)^C.

Erdős offered $250 for a proof or disproof of this statement [Er81h].
-/
theorem erdos_problem_18c :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (practicalH n.factorial : ℝ) < (Real.log (n : ℝ)) ^ C :=
  sorry
