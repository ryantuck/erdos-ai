import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section

open SimpleGraph Filter Classical

namespace Erdos1156

/-!
# Erdős Problem #1156

Let G be a random graph on n vertices, in which every edge is included
independently with probability 1/2 (the Erdős–Rényi model G(n,1/2)).

Part 1: Is there some constant C such that the chromatic number χ(G) is,
almost surely, concentrated on at most C values?

Part 2: Is it true that, if ω(n) → ∞ sufficiently slowly, then for every
function f(n), P(|χ(G) - f(n)| < ω(n)) < 1/2 if n is sufficiently large?

Bollobás proved that χ(G) ~ n/(2 log₂ n) with high probability.
Shamir and Spencer proved concentration within o(√n).
Heckel and Riordan proved concentration cannot be within n^c for c < 1/2.

A problem of Alon–Spencer [AlSp92] and Vu [Va99,3.6].

Tags: graph theory, chromatic number
-/

/-- The probability that the chromatic number of a uniformly random graph
    G(n,1/2) on n vertices satisfies predicate P. Here G(n,1/2) is the
    Erdős–Rényi model where each edge is included independently with
    probability 1/2, equivalently the uniform distribution over all simple
    graphs on n labelled vertices. -/
noncomputable def chromaticNumberProb (n : ℕ) (P : ℕ → Prop) : ℝ := sorry

/--
Erdős Problem #1156, Part 1 [AlSp92]:

There exists a constant C such that χ(G(n,1/2)) is almost surely concentrated
on at most C values. That is, for every ε > 0 and all sufficiently large n,
there is a set S of at most C natural numbers with P(χ(G) ∈ S) ≥ 1 - ε.
-/
theorem erdos_problem_1156_concentration :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        ∃ S : Finset ℕ, S.card ≤ C ∧
          chromaticNumberProb n (· ∈ S) ≥ 1 - ε :=
  sorry

/--
Erdős Problem #1156, Part 2 [AlSp92][Va99,3.6]:

There exists a function ω : ℕ → ℝ with ω(n) → ∞ such that for every function
f : ℕ → ℝ, for all sufficiently large n,
  P(|χ(G) - f(n)| < ω(n)) < 1/2.
That is, the chromatic number cannot be concentrated in any interval of width
2ω(n) with probability ≥ 1/2.
-/
theorem erdos_problem_1156_anticoncentration :
    ∃ ω : ℕ → ℝ, Tendsto ω atTop atTop ∧
      ∀ f : ℕ → ℝ, ∀ᶠ n in atTop,
        chromaticNumberProb n (fun k => |(k : ℝ) - f n| < ω n) < 1 / 2 :=
  sorry

end Erdos1156

end
