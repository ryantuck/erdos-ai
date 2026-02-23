import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

/--
The {2,3}-smooth part of a natural number n, i.e., 2^(v₂(n)) · 3^(v₃(n)),
where v_p denotes the p-adic valuation.
-/
def smoothPart23 (n : ℕ) : ℕ :=
  2 ^ padicValNat 2 n * 3 ^ padicValNat 3 n

/--
Erdős Problem #933 [Er76d]:

If n(n+1) = 2^k · 3^l · m where gcd(m, 6) = 1, is it true that
  limsup_{n → ∞} (2^k · 3^l) / (n · log n) = ∞ ?

Equivalently: for every C > 0, there exist arbitrarily large n such that
the {2,3}-smooth part of n(n+1) exceeds C · n · log n.

Mahler proved that 2^k · 3^l < n^{1+o(1)}.
Erdős wrote that 'it is easy to see' that for infinitely many n,
2^k · 3^l > n · log n.
-/
theorem erdos_problem_933 :
    ∀ C : ℝ, C > 0 →
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (smoothPart23 (n * (n + 1)) : ℝ) > C * (n : ℝ) * Real.log (n : ℝ) :=
  sorry

end
