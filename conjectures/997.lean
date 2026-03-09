import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean

open Filter Set

/-!
# Erdős Problem #997

Call $x_1, x_2, \ldots \in (0,1)$ well-distributed if, for every $\varepsilon > 0$,
if $k$ is sufficiently large then, for all $n > 0$ and intervals $I \subseteq [0,1]$,
  |#{n < m ≤ n+k : x_m ∈ I} - |I|·k| < ε·k.

Is it true that, for every α, the sequence {α·pₙ} is not well-distributed,
where pₙ is the sequence of primes?

The notion of a well-distributed sequence was introduced by Hlawka and Petersen.
-/

noncomputable section

/-- The sequence of primes in increasing order. -/
noncomputable def nthPrime : ℕ → ℕ := sorry

axiom nthPrime_prime : ∀ n, Nat.Prime (nthPrime n)
axiom nthPrime_strictMono : StrictMono nthPrime

/-- A sequence x : ℕ → ℝ (with values in [0,1]) is well-distributed if for every
    ε > 0 there exists K such that for all k ≥ K, all n ≥ 1, and all
    subintervals [a,b] ⊆ [0,1], the number of m with n < m ≤ n+k and x m ∈ [a,b]
    is within ε·k of (b-a)·k. -/
def IsWellDistributed (x : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∀ n : ℕ, 0 < n →
        ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
          |((Finset.Ioc n (n + k)).filter (fun m => x m ∈ Icc a b)).card - (b - a) * k| < ε * k

/--
Erdős Problem #997 [Er64b]:

For every real number α, the sequence {α·pₙ} (fractional parts of α times the
nth prime) is not well-distributed.
-/
theorem erdos_problem_997 :
    ∀ α : ℝ, ¬ IsWellDistributed (fun n => Int.fract (α * (nthPrime n : ℝ))) :=
  sorry

end
