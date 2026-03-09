import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1072

For any prime p, let f(p) be the least positive integer m such that
p ∣ m! + 1 (equivalently, m! ≡ -1 (mod p)).

By Wilson's theorem, (p-1)! ≡ -1 (mod p) for every prime p, so f(p) is
well-defined and f(p) ≤ p - 1.

**Part (a):** Is it true that there are infinitely many primes p for which
f(p) = p - 1?

**Part (b):** Is it true that f(p)/p → 0 for almost all primes p?

Reference: [HaSu02], [Gu04] (problem A2 in Guy's collection).
https://www.erdosproblems.com/1072
-/

/-- For a prime p, there exists m such that p ∣ m! + 1.
    By Wilson's theorem, m = p - 1 always works. -/
private lemma exists_factorial_mod (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, 0 < m ∧ p ∣ (m.factorial + 1) :=
  ⟨p - 1, Nat.sub_pos_of_lt (hp.one_lt), by sorry⟩

/-- f(p): the least positive integer m such that p ∣ m! + 1. -/
noncomputable def erdos1072_f (p : ℕ) (hp : Nat.Prime p) : ℕ :=
  Nat.find (exists_factorial_mod p hp)

/--
Erdős Problem #1072, Part (a) [HaSu02]:

There are infinitely many primes p for which f(p) = p - 1, i.e., p - 1 is
the least m with p ∣ m! + 1.
-/
theorem erdos_problem_1072a :
    Set.Infinite {p : ℕ | ∃ hp : Nat.Prime p, erdos1072_f p hp = p - 1} :=
  sorry

/-- Count of primes p ≤ N satisfying predicate P. -/
noncomputable def countPrimesSat1072 (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => Nat.Prime p ∧ P p)).card

/-- Count of primes p ≤ N. -/
noncomputable def countPrimes1072 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => Nat.Prime p)).card

/--
Erdős Problem #1072, Part (b) [HaSu02]:

f(p)/p → 0 for almost all primes p. Formulated as: for every ε > 0,
the proportion of primes p ≤ N with f(p) ≥ ε · p tends to 0 as N → ∞.

Hardy and Subbarao believed that the number of primes p ≤ x with
f(p) = p - 1 is o(x / log x).
-/
theorem erdos_problem_1072b :
    ∀ ε : ℝ, ε > 0 →
    Filter.Tendsto
      (fun N : ℕ =>
        (countPrimesSat1072
          (fun p => ∃ hp : Nat.Prime p, (erdos1072_f p hp : ℝ) ≥ ε * (p : ℝ)) N : ℝ) /
          (countPrimes1072 N : ℝ))
      atTop (nhds 0) :=
  sorry

end
