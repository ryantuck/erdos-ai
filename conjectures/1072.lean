import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.LiminfLimsup

open Set Filter

noncomputable section

/-!
# Erdős Problem #1072

For any prime p, let f(p) be the least integer such that f(p)! + 1 ≡ 0 (mod p).

Is it true that there are infinitely many p for which f(p) = p - 1?
Is it true that f(p)/p → 0 for almost all p?

By Wilson's theorem, (p-1)! ≡ -1 (mod p) for every prime p, so f(p) is
well-defined and f(p) ≤ p - 1.
-/

/-- For a prime p, the least natural number n such that p ∣ n! + 1.
    Well-defined by Wilson's theorem: (p-1)! + 1 ≡ 0 (mod p). -/
noncomputable def erdos1072_f (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  Nat.find (⟨p - 1, by sorry⟩ : ∃ n : ℕ, p ∣ n.factorial + 1)

/--
Erdős Problem #1072, Part 1:
There are infinitely many primes p for which f(p) = p - 1.
-/
theorem erdos_problem_1072a :
    Set.Infinite {p : ℕ | ∃ hp : Nat.Prime p, erdos1072_f p hp = p - 1} :=
  sorry

/-- The upper density of a set of natural numbers. -/
noncomputable def upperDensity1072 (s : Set ℕ) : ℝ :=
  limsup (fun n => ((s ∩ {i | i < n}).ncard : ℝ) / n) atTop

/--
Erdős Problem #1072, Part 2:
f(p)/p → 0 for almost all primes p. Formalized as: for every ε > 0,
the set of primes p with f(p) ≥ ε · p has upper density 0.
-/
theorem erdos_problem_1072b :
    ∀ ε : ℝ, ε > 0 →
    upperDensity1072 {p : ℕ | ∃ hp : Nat.Prime p, (erdos1072_f p hp : ℝ) ≥ ε * p} = 0 :=
  sorry

end
