import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #790

Let l(n) be maximal such that if A ⊂ ℤ with |A| = n then there exists a
sum-free B ⊆ A with |B| ≥ l(n) — that is, B is such that there are no
solutions to a₁ = a₂ + ⋯ + aᵣ with aᵢ ∈ B all distinct.

Estimate l(n). In particular, is it true that l(n)n^{-1/2} → ∞?
Is it true that l(n) < n^{1-c} for some c > 0?

Choi, Komlós, and Szemerédi [CKS75] proved
  (n log n / log log n)^{1/2} ≪ l(n) ≪ n / log n.
They further conjecture that l(n) ≥ n^{1-o(1)}.

https://www.erdosproblems.com/790

Tags: additive combinatorics
-/

/-- A finset B ⊆ ℤ is "sum-free" in the sense of Erdős #790 if no element
    of B equals the sum of two or more other distinct elements of B. -/
def SumFree790 (B : Finset ℤ) : Prop :=
  ∀ b ∈ B, ∀ S : Finset ℤ, S ⊆ B.erase b → S.card ≥ 2 → b ≠ S.sum id

/-- l(n): the largest l such that every n-element subset A of ℤ contains a
    sum-free subset B with |B| ≥ l. -/
noncomputable def erdos790_l (n : ℕ) : ℕ :=
  sSup {l : ℕ | ∀ (A : Finset ℤ), A.card = n →
    ∃ B : Finset ℤ, B ⊆ A ∧ l ≤ B.card ∧ SumFree790 B}

/--
**Erdős Problem #790** — Conjecture 1:

l(n)n^{-1/2} → ∞, i.e., for every C > 0 there exists N₀ such that
l(n) ≥ C · n^{1/2} for all n ≥ N₀.
-/
theorem erdos_problem_790_superroot :
    ∀ C : ℝ, C > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos790_l n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
**Erdős Problem #790** — Conjecture 2:

l(n) < n^{1-c} for some c > 0, i.e., there exist c > 0 and N₀ such that
l(n) ≤ n^{1-c} for all n ≥ N₀.
-/
theorem erdos_problem_790_upper :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos790_l n : ℝ) ≤ (n : ℝ) ^ (1 - c) :=
  sorry

/--
**Erdős Problem #790** — CKS lower bound [CKS75]:

l(n) ≫ (n log n / log log n)^{1/2}.
-/
theorem erdos_problem_790_CKS_lower :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos790_l n : ℝ) ≥
        C * ((n : ℝ) * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2) :=
  sorry

/--
**Erdős Problem #790** — CKS upper bound [CKS75]:

l(n) ≪ n / log n.
-/
theorem erdos_problem_790_CKS_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos790_l n : ℝ) ≤ C * ((n : ℝ) / Real.log (n : ℝ)) :=
  sorry

/--
**Erdős Problem #790** — CKS conjecture [CKS75]:

l(n) ≥ n^{1-o(1)}, i.e., for every ε > 0, there exists N₀ such that
l(n) ≥ n^{1-ε} for all n ≥ N₀.
-/
theorem erdos_problem_790_CKS_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos790_l n : ℝ) ≥ (n : ℝ) ^ (1 - ε) :=
  sorry

end
