import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

/-!
# Erdős Problem #650

Let f(m) be such that if A ⊆ {1,…,N} has |A| = m then every interval in
[1,∞) of length 2N contains ≥ f(m) many distinct integers b₁,…,bᵣ where
each bᵢ is divisible by some aᵢ ∈ A, where a₁,…,aᵣ are distinct.

Estimate f(m). In particular is it true that f(m) ≪ m^{1/2}?

Erdős and Sarányi [ErSa59] proved that f(m) ≫ m^{1/2}.

Reference: [Er95c]
https://www.erdosproblems.com/650
-/

/-- The divisibility matching number: given a finite set A of positive integers,
    a starting point t ≥ 1, and a parameter N, this is the maximum r such that
    there exist r distinct integers b₁,...,bᵣ in [t, t + 2N) and r distinct
    elements a₁,...,aᵣ ∈ A with aᵢ ∣ bᵢ. -/
def divMatchCount (A : Finset ℕ) (t N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ (b a : Fin r → ℕ),
    Function.Injective b ∧ Function.Injective a ∧
    (∀ i, a i ∈ A) ∧
    (∀ i, t ≤ b i ∧ b i < t + 2 * N) ∧
    (∀ i, a i ∣ b i)}

/-- f(m): the largest value guaranteed in all configurations. For every N ≥ 1
    and every m-element subset A of {1,...,N}, every interval [t, t+2N) with
    t ≥ 1 contains at least f(m) matchable integers. -/
def erdos650_f (m : ℕ) : ℕ :=
  sInf {c : ℕ | ∃ (N : ℕ) (A : Finset ℕ) (t : ℕ),
    A.card = m ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ t ≥ 1 ∧
    divMatchCount A t N = c}

/--
Erdős Problem #650 [Er95c]:

Is it true that f(m) ≪ m^{1/2}? Erdős and Sarányi [ErSa59] proved f(m) ≫ m^{1/2},
so this would establish f(m) ≍ m^{1/2}.

Formalised as: there exists C > 0 such that f(m) ≤ C · √m for all
sufficiently large m.
-/
theorem erdos_problem_650 :
    ∃ C : ℝ, 0 < C ∧
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m →
      (erdos650_f m : ℝ) ≤ C * Real.sqrt (m : ℝ) :=
  sorry

end
