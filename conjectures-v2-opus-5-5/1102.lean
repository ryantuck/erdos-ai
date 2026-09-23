-- [AI-Generated]: Erdős Problem 1102 — second-pass formalization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Filter

namespace Erdos1102

/-!
# Erdős Problem #1102

*Source:* [erdosproblems.com/1102](https://www.erdosproblems.com/1102) (status
**SOLVED (LEAN)**: "This has been resolved in some other way than a proof or disproof, and
that resolution verified in Lean."; page last edited 02 December 2025, captured
2026-03-09). [Er81h, p.179]

We say that A ⊆ ℕ has property P if, for all n ≥ 1, there are only finitely many
a ∈ A such that n + a is squarefree.

We say that A has property Q if there are infinitely many n such that n + a is
squarefree for all a ∈ A with a < n. (The page writes "for all $a < n$"; the
restriction to `a ∈ A` is the only reading under which Q depends on A.)

How fast must sequences A = {a₁ < a₂ < ⋯} with properties P or Q increase?

Resolved by van Doorn and Tao [vDTa25]:
- Any sequence with property P has density 0, but density can go to 0 arbitrarily slowly.
- Any sequence with property Q has upper density at most 6/π², and this is achievable.

Further remarks on the source page:
- Erdős [Er81h] notes it is easy to see that there exist A with property P, and that any
  set which increases sufficiently quickly has property Q.
- He also asks about property P′ (infinitely many n such that n + a is squarefree for
  all a ∈ A) and property P′_∞ (infinitely many n such that n + a is squarefree for all
  but finitely many a ∈ A). van Doorn and Tao show that any sequence with property P′ or
  P′_∞ has upper density < 6/π², and that this is best possible: for any ε > 0 there
  exist such sequences with lower density > 6/π² − ε. See the `variants` below.
- Erdős also asks whether special sequences such as 2ⁿ ± 1 or n! ± 1 have properties P
  or Q. van Doorn and Tao show that 2ⁿ ± 1 and n! ± 1 have property Q; it remains open
  whether these sequences have property P. (Not formalized: the page does not fix the
  range of n, which matters for Q through the smallest terms, and n! is not among this
  file's constructs.)

Tags: number theory. OEIS: none listed. The page records an upstream formalised
statement (google-deepmind/formal-conjectures); this file is independent of it.

## References

- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number
  theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.
- [vDTa25] W. van Doorn and T. Tao, _Growth rates of sequences governed by the squarefree
  properties of its translates_. arXiv:2512.01087 (2025).

(Both entries as extracted by the original pipeline's fetch of
`erdosproblems.com/latex/1103`, which cites the same two keys. A gloss of [vDTa25] as
"van Doorn, F. and Tao, T., _Sumsets of squarefree numbers_ (2025)" circulates in this
repository's logs; it is wrong on both the initial and the title.)
-/

/-- Property P: for all n ≥ 1, only finitely many a ∈ A satisfy "n + a is squarefree". -/
def HasPropertyP (A : Set ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → Set.Finite {a ∈ A | Squarefree (n + a)}

/-- Property Q: infinitely many n such that n + a is squarefree for all a ∈ A with a < n. -/
def HasPropertyQ (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | ∀ a ∈ A, a < n → Squarefree (n + a)}

/-- Property P′: infinitely many n such that n + a is squarefree for *all* a ∈ A.
(P′ implies both Q and P′_∞.) -/
def HasPropertyP' (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | ∀ a ∈ A, Squarefree (n + a)}

/-- Property P′_∞: infinitely many n such that n + a is squarefree for all but finitely
many a ∈ A. -/
def HasPropertyPInfty (A : Set ℕ) : Prop :=
  Set.Infinite {n : ℕ | Set.Finite {a ∈ A | ¬ Squarefree (n + a)}}

/-- The counting function for a set S ⊆ ℕ up to N (it counts `S ∩ [0, N]`). -/
noncomputable def countingFn (S : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (S ∩ Set.Iic N)

/-- The upper density of a set S ⊆ ℕ. The ratio `|S ∩ [0, N]| / (N + 1)` lies in
`[0, 1]`, so the `limsup` is a genuine one, and it agrees with the usual
`limsup |S ∩ [1, N]| / N` (the two ratios differ by `O(1/N)`). -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop

/-- The natural density of a set S ⊆ ℕ equals d if the ratio converges to d. -/
def hasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (countingFn S N : ℝ) / (N + 1 : ℝ)) atTop (nhds d)

/-- Erdős Problem #1102, Part 1 (SOLVED) [Er81h, vDTa25]:

Any strictly increasing sequence with property P has density 0.
Equivalently, a(j)/j → ∞. -/
theorem density_zero_of_P (a : ℕ → ℕ) (ha : StrictMono a)
    (hP : HasPropertyP (Set.range a)) :
    Tendsto (fun j : ℕ => (a j : ℝ) / (j : ℝ)) atTop atTop :=
  sorry

/-- Erdős Problem #1102, Part 2 (SOLVED) [Er81h, vDTa25]:

For any function f going to infinity, there exists a strictly increasing sequence
with property P such that a(j) ≤ f(j) · j for all sufficiently large j, i.e. a(j)/j
tends to infinity (Part 1) no faster than f. That is, density can go to 0 arbitrarily
slowly.

The bound is required only eventually. The first-pass file required it for every j,
which is false: for f(j) = log(j + 1), j = 1 forces a(1) ≤ log 2 < 1, so a(1) = 0,
contradicting a(0) < a(1). -/
theorem exists_sequence_with_P (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ HasPropertyP (Set.range a) ∧
      ∀ᶠ j : ℕ in atTop, (a j : ℝ) ≤ f j * (j : ℝ) :=
  sorry

/-- Erdős Problem #1102, Part 3 (SOLVED) [Er81h, vDTa25]:

Any set with property Q has upper density at most 6/π². -/
theorem upper_density_Q (A : Set ℕ) (hQ : HasPropertyQ A) :
    upperDensity A ≤ 6 / Real.pi ^ 2 :=
  sorry

/-- Erdős Problem #1102, Part 4 (SOLVED) [Er81h, vDTa25]:

There exists an infinite set with property Q and natural density equal to 6/π². -/
theorem exists_Q_with_max_density :
    ∃ A : Set ℕ, Set.Infinite A ∧ HasPropertyQ A ∧
      hasNaturalDensity A (6 / Real.pi ^ 2) :=
  sorry

/-- [vDTa25]: any set with property P′ has upper density strictly less than 6/π².
(Also a consequence of `variants.upper_density_PInfty_lt`, since P′ implies P′_∞.) -/
theorem variants.upper_density_PPrime_lt (A : Set ℕ) (hA : HasPropertyP' A) :
    upperDensity A < 6 / Real.pi ^ 2 :=
  sorry

/-- [vDTa25]: any set with property P′_∞ has upper density strictly less than 6/π². -/
theorem variants.upper_density_PInfty_lt (A : Set ℕ) (hA : HasPropertyPInfty A) :
    upperDensity A < 6 / Real.pi ^ 2 :=
  sorry

/-- [vDTa25]: the bound `< 6/π²` is best possible. For every ε > 0 there is a set with
property P′_∞ whose lower density exceeds 6/π² − ε. Here "lower density > L" is written as
`∃ c > L, eventually c ≤ |A ∩ [0, N]| / (N + 1)`, which is equivalent to `liminf > L`.

The page says "there exist such sequences" after naming both P′ and P′_∞. This takes the
weaker reading (P′_∞). The stronger reading, a P′ example, would imply it. -/
theorem variants.exists_PInfty_lower_density_near_max (ε : ℝ) (hε : 0 < ε) :
    ∃ A : Set ℕ, HasPropertyPInfty A ∧ ∃ c : ℝ, 6 / Real.pi ^ 2 - ε < c ∧
      ∀ᶠ N : ℕ in atTop, c ≤ (countingFn A N : ℝ) / (N + 1 : ℝ) :=
  sorry

end Erdos1102

end
