import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #1136

Does there exist A ⊆ ℕ with lower density > 1/3 such that a + b ≠ 2^k for
any a, b ∈ A and k ≥ 0?

Status on erdosproblems.com/1136: PROVED ("This has been solved in the
affirmative."). Page last edited 20 January 2026, accessed 2026-02-23.
Tag: number theory. No related OEIS sequences listed on the page.

A question asked by Erdős at the DMV conference in Berlin 1987 (as reported
in [Mu11]). Achieving density 1/3 is trivial, taking A to be all multiples
of 3.

Müller [Mu11] settled this question in the affirmative: in fact one can take
A to be the set of all integers congruent to 3 · 2^i (mod 2^{i+2}) for any
i ≥ 0, which has density 1/2. Müller also proved this is best possible, in
that A with the property in the question has lower density at most 1/2.

References (the page's sole citation key is [Mu11]; bibliographic data
recovered from the original pipeline's fetch of erdosproblems.com/latex/1136
captured in the session logs; the volume number was absent from the
recovered data and is deliberately not invented — DEFERRED):

- [Mu11] Müller, H. (Helmut), _Über ein additiv-zahlentheoretisches Problem
  von P. Erdős_. Mitteilungen der Mathematischen Gesellschaft in Hamburg
  (2011), 75–78.

NOTE: the two definitions and the main theorem statement below are unchanged
from the input file (`conjectures/1136.lean`) — the Fable review of
2026-08-14 found no semantic defects in them (the eventual-bound encoding of
"lower density > 1/3" is equivalent to liminf |A ∩ [1, N]|/N > 1/3). That
review added this bibliography and status record, the two page-confirmed
variant statements below, and dropped a redundant `Finset.` qualifier under
the existing `open Finset`. The file is NOT compile-verified in this
container.
-/

/-- A set A ⊆ ℕ is power-of-2 sum-free if no two elements (not necessarily
    distinct) sum to a power of 2. -/
def PowerOfTwoSumFree (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The counting function |A ∩ [1, N]| for a set A ⊆ ℕ. -/
noncomputable def countInInterval1136 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).filter (· ∈ A)).card

/--
Erdős Problem #1136 (PROVED — settled in the affirmative by Müller [Mu11]):
There exists A ⊆ ℕ with lower density strictly greater than 1/3 such that
no two elements of A sum to a power of 2.

The lower density condition is formalized as: there exist δ > 1/3 and N₀
such that |A ∩ [1, N]| ≥ δ · N for all N ≥ N₀. This is equivalent to
liminf_{N→∞} |A ∩ [1, N]|/N > 1/3: any such δ eventually bounds the ratio
from below, so the liminf is ≥ δ > 1/3; conversely any δ strictly between
1/3 and the liminf eventually satisfies |A ∩ [1, N]|/N ≥ δ.

Stated as a direct assertion of the asked ("yes") direction per this
corpus's raw-file convention; a styled version would use `answer(True) ↔`.
-/
theorem erdos_problem_1136 :
    ∃ (A : Set ℕ),
      PowerOfTwoSumFree A ∧
      ∃ (δ : ℝ), δ > 1/3 ∧
        ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ →
          δ * (N : ℝ) ≤ (countInInterval1136 A N : ℝ) :=
  sorry

/-- Müller's witness set [Mu11]: all n ∈ ℕ congruent to 3 · 2^i (mod 2^{i+2})
    for some i ≥ 0. Since 3 · 2^i < 2^{i+2}, the congruence is written as
    `n % 2 ^ (i + 2) = 3 * 2 ^ i`. Every element has the form 2^i · (4m + 3),
    so the classes for distinct i are disjoint and the set has natural
    density ∑_{i ≥ 0} 2^{-(i+2)} = 1/2. -/
def muellerSet1136 : Set ℕ :=
  {n : ℕ | ∃ i : ℕ, n % 2 ^ (i + 2) = 3 * 2 ^ i}

/--
Variant (page-confirmed) — Müller's explicit construction [Mu11]: the set of
all integers congruent to 3 · 2^i (mod 2^{i+2}) for some i ≥ 0 is power-of-2
sum-free and has natural density 1/2.

The density condition is formalized as the two-sided eventual bound
(1/2 − ε) · N ≤ |A ∩ [1, N]| ≤ (1/2 + ε) · N for every ε > 0, i.e.
|A ∩ [1, N]|/N → 1/2 (full natural density, as the page states — not merely
lower density 1/2). NOTE: new statement written by the 2026-08-14 Fable
review from the recovered page content; NOT compile-verified.
-/
theorem erdos_problem_1136_construction :
    PowerOfTwoSumFree muellerSet1136 ∧
    ∀ ε : ℝ, ε > 0 →
      ∃ (N₀ : ℕ), ∀ (N : ℕ), N ≥ N₀ →
        (1/2 - ε) * (N : ℝ) ≤ (countInInterval1136 muellerSet1136 N : ℝ) ∧
        (countInInterval1136 muellerSet1136 N : ℝ) ≤ (1/2 + ε) * (N : ℝ) :=
  sorry

/--
Variant (page-confirmed) — Müller's optimality result [Mu11]: any A with the
property in the question has lower density at most 1/2.

"Lower density ≤ 1/2" is stated as the unfolding of the negation of the main
theorem's encoding at threshold 1/2: for every δ > 1/2 and every N₀ there is
some N ≥ N₀ with |A ∩ [1, N]| < δ · N. This is equivalent to
liminf_{N→∞} |A ∩ [1, N]|/N ≤ 1/2: if the liminf exceeded some δ > 1/2 the
ratio would eventually stay ≥ δ, and conversely ratios < δ infinitely often
for every δ > 1/2 force the liminf ≤ 1/2. NOTE: new statement written by the
2026-08-14 Fable review from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_1136_upper (A : Set ℕ) (hA : PowerOfTwoSumFree A) :
    ∀ δ : ℝ, δ > 1/2 → ∀ N₀ : ℕ, ∃ N : ℕ, N ≥ N₀ ∧
      (countInInterval1136 A N : ℝ) < δ * (N : ℝ) :=
  sorry

end
