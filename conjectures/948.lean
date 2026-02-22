import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-!
# Erdős Problem #948

Is there a function $f(n)$ and a $k$ such that in any $k$-colouring of the
integers there exists a sequence $a_1 < a_2 < \cdots$ such that $a_n < f(n)$
for infinitely many $n$ and the set
$$\left\{ \sum_{i \in S} a_i : S \text{ finite} \right\}$$
does not contain all colours?

Erdős initially asked whether this is possible with the set being monochromatic,
but Galvin showed that this is not always possible. This is a variant of
Hindman's theorem (see [532]).
-/

/-- **Erdős Problem #948** (OPEN):
There exist a function `f : ℕ → ℕ` and `k : ℕ` such that for any `k`-colouring
`χ` of the natural numbers, there is a strictly increasing sequence `a` with
`a n < f n` for infinitely many `n`, and the finite subset sums of the sequence
do not achieve all `k` colours. -/
theorem erdos_problem_948 :
    ∃ (f : ℕ → ℕ) (k : ℕ), 0 < k ∧
    ∀ (χ : ℕ → Fin k),
      ∃ (a : ℕ → ℕ), StrictMono a ∧
        Set.Infinite {n : ℕ | a n < f n} ∧
        ∃ (c : Fin k), ∀ (S : Finset ℕ), S.Nonempty →
          χ (∑ i ∈ S, a i) ≠ c :=
  sorry
