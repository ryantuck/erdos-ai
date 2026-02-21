import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Finset

/-- The k-fold iteration of Euler's totient function.
    Applies φ to n exactly k times: φ^[0](n) = n, φ^[k](n) = φ(φ^[k-1](n)). -/
def iteratedTotient (k n : ℕ) : ℕ := Nat.totient^[k] n

/-- f(n) = min{k : φ^[k](n) = 1}, the number of iterations of Euler's totient
    function needed to reach 1. Returns 0 for n ≤ 1.
    This is well-defined for n ≥ 2 since φ(m) < m for m ≥ 2 and φ(1) = 1. -/
noncomputable def totientIterationLength (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.find (⟨n, by sorry⟩ : ∃ k, iteratedTotient k n = 1)

/--
Erdős Problem #408 [ErGr80] — OPEN

Let φ(n) be the Euler totient function and φ_k(n) be the k-fold iterate of φ,
so that φ_1(n) = φ(n) and φ_k(n) = φ(φ_{k-1}(n)). Let
  f(n) = min{k : φ_k(n) = 1}.

Part (a): f(n)/log(n) has a distribution function, i.e., for every real c,
the natural density of {n ≤ N : f(n)/log(n) ≤ c} exists.

Erdős, Granville, Pomerance, and Spiro [EGPS90] proved this conditional on a
form of the Elliott-Halberstam conjecture.
-/
theorem erdos_problem_408a :
    ∀ c : ℝ,
      ∃ d : ℝ, Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun n =>
            (totientIterationLength n : ℝ) / Real.log n ≤ c)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds d) :=
  sorry

/--
Erdős Problem #408 [ErGr80] — OPEN

Part (b): f(n)/log(n) is almost always equal to some constant α > 0, i.e.,
there exists α > 0 such that for all ε > 0, the natural density of
{n : |f(n)/log(n) - α| ≥ ε} is zero.

It is expected that α = 1/log(2). Erdős, Granville, Pomerance, and Spiro
[EGPS90] proved this conditional on a form of the Elliott-Halberstam conjecture.
-/
theorem erdos_problem_408b :
    ∃ α : ℝ, α > 0 ∧
      ∀ ε : ℝ, ε > 0 →
        Filter.Tendsto
          (fun N : ℕ =>
            (((Finset.range N).filter (fun n =>
              ε ≤ |((totientIterationLength n : ℝ) / Real.log n) - α|)).card : ℝ) / (N : ℝ))
          Filter.atTop (nhds 0) :=
  sorry
