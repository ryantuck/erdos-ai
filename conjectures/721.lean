import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

/--
An arithmetic progression of length `j` with first term `a` and common
difference `d` lies in `{0, ..., n-1}` if `d ≥ 1` and all terms
`a + i * d` for `i < j` are less than `n`.
-/
def APInRange (n a d j : ℕ) : Prop :=
  d ≥ 1 ∧ ∀ i < j, a + i * d < n

/--
A 2-coloring `f : ℕ → Bool` of `{0, ..., n-1}` has a monochromatic
`j`-term arithmetic progression in color `c`.
-/
def HasMonoAP (f : ℕ → Bool) (n j : ℕ) (c : Bool) : Prop :=
  ∃ a d, APInRange n a d j ∧ ∀ i < j, f (a + i * d) = c

/--
`VDWProperty j k n` asserts: every 2-coloring of `{0, ..., n-1}` contains
either a monochromatic `j`-AP in one color or a monochromatic `k`-AP in
the other.
-/
def VDWProperty (j k n : ℕ) : Prop :=
  ∀ f : ℕ → Bool, HasMonoAP f n j true ∨ HasMonoAP f n k false

/--
The van der Waerden number `W(j, k)` is the smallest `n` such that
`VDWProperty j k n` holds. Defined as the infimum of all such `n`.
Van der Waerden's theorem guarantees this set is nonempty for `j, k ≥ 1`.
-/
noncomputable def vanDerWaerden (j k : ℕ) : ℕ :=
  sInf {n : ℕ | VDWProperty j k n}

/--
Erdős Problem #721 (Upper Bound):
There exists a constant `c` with `0 < c < 1` such that for all sufficiently
large `k`, `W(3, k) < exp(k^c)`.

This was first proved by Schoen [Sc21]. The best known upper bound is
`W(3, k) ≤ exp(O((log k)^9))` due to Bloom-Sisask [BlSi23], improving
on Kelley-Meka [KeMe23].
-/
theorem erdos_problem_721_upper_bound :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ N₀ : ℕ, ∀ k : ℕ, k ≥ N₀ →
    (vanDerWaerden 3 k : ℝ) < Real.exp ((k : ℝ) ^ c) :=
  sorry

/--
Erdős Problem #721 (Lower Bound):
`W(3, k)` grows superpolynomially: for every degree `d`,
`W(3, k) > k^d` for all sufficiently large `k`.

Green [Gr22] proved `W(3,k) ≥ exp(c(log k)^{4/3}/(log log k)^{1/3})`,
improved by Hunter [Hu22] to `W(3,k) ≥ exp(c(log k)²/log log k)`.
-/
theorem erdos_problem_721_lower_bound :
    ∀ d : ℕ, ∃ N₀ : ℕ, ∀ k : ℕ, k ≥ N₀ →
    (vanDerWaerden 3 k : ℝ) > (k : ℝ) ^ (d : ℝ) :=
  sorry
