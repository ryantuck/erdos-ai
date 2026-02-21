import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

/-!
# Erdős Problem #241

Let f(N) be the maximum size of A ⊆ {1,...,N} such that the sums a+b+c with
a,b,c ∈ A are all distinct (aside from the trivial coincidences). Is it true
that f(N) ~ N^{1/3}?

A set with this property is called a B₃ set (or Sidon set of order 3).

Originally asked to Erdős by Bose. Bose and Chowla [BoCh62] proved the lower
bound (1+o(1))N^{1/3} ≤ f(N). The best known upper bound is due to Green [Gr01]:
f(N) ≤ ((7/2)^{1/3}+o(1))N^{1/3}.

$100 prize.
-/

/-- A finite set A ⊆ ℕ is a *B₃ set* if whenever a₁ + a₂ + a₃ = b₁ + b₂ + b₃
    with all elements from A (in sorted order), then the two triples are identical.
    Equivalently, all 3-element sums are distinct up to reordering. -/
def IsB3Set (A : Finset ℕ) : Prop :=
  ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℕ,
    a₁ ∈ A → a₂ ∈ A → a₃ ∈ A → b₁ ∈ A → b₂ ∈ A → b₃ ∈ A →
    a₁ ≤ a₂ → a₂ ≤ a₃ → b₁ ≤ b₂ → b₂ ≤ b₃ →
    a₁ + a₂ + a₃ = b₁ + b₂ + b₃ →
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃

/-- f(N) is the maximum cardinality of a B₃ subset of {1,...,N}. -/
noncomputable def erdos241F (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsB3Set A ∧ A.card = k}

/--
Erdős Problem #241 [Er61, Er69, Er70b, Er70c, Er73, Er77c, ErGr80]:
Let f(N) be the maximum size of a B₃ subset of {1,...,N}. Then f(N) ~ N^{1/3},
i.e., the ratio f(N)/N^{1/3} tends to 1 as N → ∞.

Known bounds:
- (1+o(1))N^{1/3} ≤ f(N)            (Bose–Chowla [BoCh62])
- f(N) ≤ ((7/2)^{1/3}+o(1))N^{1/3}  (Green [Gr01])
-/
theorem erdos_problem_241 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (erdos241F N : ℝ) ∧
        (erdos241F N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  sorry
