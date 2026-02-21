import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Real

noncomputable section

/-!
# Erdős Problem #190

Let H(k) be the smallest N such that in any finite colouring of {1,…,N}
(into any number of colours) there is always either a monochromatic k-term
arithmetic progression or a rainbow arithmetic progression (i.e. all
elements are different colours). Estimate H(k). Is it true that
H(k)^{1/k}/k → ∞ as k → ∞?

This type of problem belongs to 'canonical' Ramsey theory. The existence
of H(k) follows from Szemerédi's theorem, and it is easy to show that
H(k)^{1/k} → ∞.
-/

/-- A colouring χ : ℕ → ℕ has a monochromatic k-term arithmetic progression
    within {1,…,N}: there exist a ≥ 1 and d ≥ 1 such that a, a+d, …,
    a+(k-1)·d are all in {1,…,N} and all share the same colour. -/
def hasMonoAP (χ : ℕ → ℕ) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
    ∀ i : ℕ, i < k → χ (a + i * d) = χ a

/-- A colouring χ : ℕ → ℕ has a rainbow 3-term arithmetic progression
    within {1,…,N}: there exist a ≥ 1 and d ≥ 1 such that a, a+d, a+2d
    are all in {1,…,N} and their colours are pairwise distinct. -/
def hasRainbowAP (χ : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + 2 * d ≤ N ∧
    χ a ≠ χ (a + d) ∧ χ a ≠ χ (a + 2 * d) ∧ χ (a + d) ≠ χ (a + 2 * d)

/-- H(k) is the smallest N such that any colouring of {1,…,N} contains
    either a monochromatic k-term AP or a rainbow 3-term AP. -/
noncomputable def H (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ χ : ℕ → ℕ, hasMonoAP χ N k ∨ hasRainbowAP χ N}

/--
Erdős Problem #190 [ErGr79, ErGr80]:

H(k)^{1/k}/k → ∞ as k → ∞, where H(k) is the smallest N such that
any finite colouring of {1,…,N} always contains either a monochromatic
k-term arithmetic progression or a rainbow arithmetic progression.
-/
theorem erdos_problem_190 :
    Tendsto (fun k : ℕ => (H k : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k : ℝ)) atTop atTop :=
  sorry

end
