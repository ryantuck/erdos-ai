import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Erdős Problem #482: Graham–Pollak Sequence and Binary Digits of √2

Define a sequence by a₁ = 1 and a_{n+1} = ⌊√2 · (aₙ + 1/2)⌋ for n ≥ 1.
Graham and Pollak [GrPo70] showed that the difference a_{2n+1} − 2·a_{2n−1}
equals the nth digit in the binary expansion of √2.

Erdős and Graham [ErGr80, p.96] asked for similar results for θ = √m and
other algebraic numbers. This was addressed by the wide-ranging
generalisations of Stoll [St05, St06].

We formalise the original Graham–Pollak result for √2.
-/

/-- The Graham–Pollak sequence: a(1) = 1, a(n+1) = ⌊√2 · (a(n) + 1/2)⌋.
    This sequence is 1-indexed; a(0) is a dummy value. -/
noncomputable def grahamPollakSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ⌊Real.sqrt 2 * ((grahamPollakSeq (n + 1) : ℝ) + 1 / 2)⌋

/-- The nth binary digit (0-indexed) of a nonnegative real number x.
    Position 0 is the integer-part bit. Equals ⌊x · 2^n⌋ mod 2. -/
noncomputable def binaryDigit (x : ℝ) (n : ℕ) : ℤ :=
  ⌊x * (2 : ℝ) ^ n⌋ % 2

/--
Erdős Problem #482 (Graham–Pollak theorem) [ErGr80, p.96]:

Define a sequence by a₁ = 1 and a_{n+1} = ⌊√2 · (aₙ + 1/2)⌋ for n ≥ 1.
Then the difference a_{2n+1} − 2·a_{2n−1} equals the nth digit in the binary
expansion of √2 (1-indexed, n ≥ 1).

The result for √2 was proved by Graham and Pollak [GrPo70]. Erdős and Graham
asked for similar results for θ = √m and other algebraic numbers; this was
addressed by the generalisations of Stoll [St05, St06].

Formalised using 0-indexed binary digits (position 0 = integer part) and
shifting the index to avoid natural-number subtraction:
for all n, a(2n+3) − 2·a(2n+1) = binaryDigit(√2, n).
-/
theorem erdos_problem_482 :
    ∀ n : ℕ,
      grahamPollakSeq (2 * n + 3) - 2 * grahamPollakSeq (2 * n + 1) =
        binaryDigit (Real.sqrt 2) n :=
  sorry
