import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

/-!
# Erdős Problem #320

Let `S(N)` count the number of distinct sums of the form `∑_{n ∈ A} 1/n`
for `A ⊆ {1, …, N}`. Estimate `S(N)`.

## Known Bounds

Bleicher and Erdős proved:
* **Lower bound** [BlEr75]: `log S(N) ≥ (N/log N)(log 2 · ∏_{i=3}^{k} log_i N)`
* **Upper bound** [BlEr76b]: `log S(N) ≤ (N/log N)(log_r N · ∏_{i=3}^{r} log_i N)`

where `log_i` denotes the `i`-fold iterated logarithm.

Bettin, Grenié, Molteni, and Sanna [BGMS25] improved the lower bound to:
  `log S(N) ≥ (N/log N)(2 log 2 (1 − 3/(2 log_k N)) · ∏_{i=3}^{k} log_i N)`

## Formalized Conjecture

We conjecture that `log S(N)` is asymptotic to a constant times
`(N / log N) · log log N`, i.e., that the ratio
`log S(N) / ((N / log N) · log log N)` converges to a positive constant.
This would pin down the leading-order asymptotics of `S(N)` and close the
gap between the known upper bound `O((N / log N) · log log N)` [BlEr76b]
and the lower bound `Ω((N / log N) · log log log N)` [BlEr75, BGMS25].
-/

/-- The set of all unit-fraction subset sums from `{1, …, N}`:
    `{ ∑_{n ∈ A} 1/n : A ⊆ {1, …, N} }` as a finite set of rationals. -/
noncomputable def unitFractionSums (N : ℕ) : Finset ℚ :=
  (Finset.Icc 1 N).powerset.image
    (fun A => A.sum (fun n => (1 : ℚ) / ↑n))

/-- `erdos320_S N` counts the number of distinct sums `∑_{n ∈ A} 1/n`
    for `A ⊆ {1, …, N}`. -/
noncomputable def erdos320_S (N : ℕ) : ℕ := (unitFractionSums N).card

/--
**Erdős Problem #320** [ErGr80, p.43]:

The ratio `log S(N) / ((N / log N) · log log N)` converges to a positive
constant as `N → ∞`. Equivalently, `log S(N) ~ L · (N / log N) · log log N`
for some `L > 0`.
-/
theorem erdos_problem_320 :
    ∃ L : ℝ, 0 < L ∧
      Filter.Tendsto
        (fun N : ℕ => Real.log (erdos320_S N : ℝ) /
          ((N : ℝ) / Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))
        Filter.atTop (nhds L) :=
  sorry
