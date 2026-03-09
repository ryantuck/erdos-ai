import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Basic

open Finset Nat Filter Classical

noncomputable section

/--
The gcd of {i^n - 1 : 2 ≤ i ≤ k}.
-/
def seqGcd (n k : ℕ) : ℕ :=
  (Finset.Icc 2 k).gcd (fun i => i ^ n - 1)

/--
h(n) is the minimal k ≥ 2 such that gcd(2^n - 1, 3^n - 1, ..., k^n - 1) = 1.
Returns 0 if no such k exists (which should not happen for n ≥ 1).
-/
noncomputable def erdos770_h (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, 2 ≤ k ∧ seqGcd n k = 1 then Nat.find h
  else 0

/--
Erdős Problem #770 (Part 1) [Er74b]:

Let h(n) be the minimal k ≥ 2 such that 2^n - 1, 3^n - 1, ..., k^n - 1 are
collectively coprime (their gcd is 1).

For every prime p, the natural density of {n : h(n) = p} exists.
-/
theorem erdos_problem_770a :
    ∀ p : ℕ, p.Prime →
      ∃ δ : ℝ, Filter.Tendsto
        (fun N => (((Finset.Icc 1 N).filter (fun n => erdos770_h n = p)).card : ℝ) / N)
        Filter.atTop (nhds δ) :=
  sorry

/--
Erdős Problem #770 (Part 2) [Er74b]:

Does lim inf h(n) = ∞? Equivalently, for every bound M, all sufficiently large
n satisfy h(n) ≥ M.
-/
theorem erdos_problem_770b :
    ∀ M : ℕ, ∀ᶠ n in Filter.atTop, erdos770_h n ≥ M :=
  sorry

/--
Erdős Problem #770 (Part 3) [Er74b]:

If p is the greatest prime such that p - 1 ∣ n and p > n^ε, then h(n) = p.
-/
theorem erdos_problem_770c :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in Filter.atTop,
        ∀ p : ℕ, p.Prime →
          (p - 1 ∣ n) →
          ((p : ℝ) > (n : ℝ) ^ ε) →
          (∀ q : ℕ, q.Prime → (q - 1 ∣ n) → ((q : ℝ) > (n : ℝ) ^ ε) → q ≤ p) →
          erdos770_h n = p :=
  sorry

end
