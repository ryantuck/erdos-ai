import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open Nat Real Filter

noncomputable section

/--
A prime chain is a strictly increasing sequence of primes where each
successive prime is congruent to 1 modulo its predecessor.
-/
def IsPrimeChain (p : ℕ → ℕ) : Prop :=
  (∀ k, Nat.Prime (p k)) ∧
  (StrictMono p) ∧
  (∀ k, p (k + 1) % p k = 1)

/--
Erdős Problem #695 [Er79e]:

Let p₁ < p₂ < ⋯ be a sequence of primes such that p_{i+1} ≡ 1 (mod p_i)
(a "prime chain"). Is it true that lim_k p_k^{1/k} = ∞?

This asks whether every prime chain must grow superexponentially.
-/
theorem erdos_problem_695a
    (p : ℕ → ℕ)
    (hp : IsPrimeChain p) :
    Tendsto (fun k : ℕ => (p k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop :=
  sorry

/--
Erdős Problem #695 (second part) [Er79e]:

Does there exist a prime chain with p_k ≤ exp(k · (log k)^{1+o(1)})?

Equivalently: for every ε > 0, there exists a prime chain such that for all
sufficiently large k, p_k ≤ exp(k · (log k)^{1+ε}).
-/
theorem erdos_problem_695b :
    ∀ ε : ℝ, 0 < ε →
      ∃ p : ℕ → ℕ, IsPrimeChain p ∧
        ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
          (p k : ℝ) ≤ Real.exp ((k : ℝ) * (Real.log (k : ℝ)) ^ (1 + ε)) :=
  sorry

end
