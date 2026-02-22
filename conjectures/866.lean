import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #866

Let k ≥ 3 and g_k(N) be minimal such that if A ⊆ {1, …, 2N} has |A| ≥ N + g_k(N)
then there exist integers b₁, …, b_k such that all C(k,2) pairwise sums bᵢ + bⱼ
are in A (but the bᵢ themselves need not be in A).

Estimate g_k(N).

A problem of Choi, Erdős, and Szemerédi [CES75].

Known results:
- g₃(N) = 2 and g₄(N) ≤ 2032
- g₅(N) ≍ log N and g₆(N) ≍ N^{1/2}
- g_k(N) ≪_k N^{1 - 2^{-k}} for all k ≥ 3
- For every ε > 0, if k is sufficiently large then g_k(N) > N^{1-ε}
-/

/-- A finset A of integers contains all pairwise sums of some k integers: there exist
    b₁, …, b_k ∈ ℤ such that bᵢ + bⱼ ∈ A for all i < j. -/
def hasPairwiseSumsIn866 (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, ∀ i j : Fin k, i < j → (b i + b j) ∈ A

/-- `gPairwiseSum866 k N` is the minimal g ∈ ℕ such that every A ⊆ {1, …, 2N} with
    |A| ≥ N + g contains all pairwise sums of some k integers. -/
noncomputable def gPairwiseSum866 (k N : ℕ) : ℕ :=
  sInf {g : ℕ | ∀ A : Finset ℤ,
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ 2 * (N : ℤ)) →
    A.card ≥ N + g → hasPairwiseSumsIn866 A k}

/--
Erdős Problem #866 [CES75]: g₃(N) = 2 for all sufficiently large N.
-/
theorem erdos_problem_866_g3 :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → gPairwiseSum866 3 N = 2 :=
  sorry

/--
Erdős Problem #866, upper bound [CES75]:

For every k ≥ 3, g_k(N) ≪_k N^{1 - 2^{-k}}, i.e., there exists a constant C > 0
(depending on k) such that g_k(N) ≤ C · N^{1 - 1/2^k} for all N ≥ 1.
-/
theorem erdos_problem_866_upper (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
      (gPairwiseSum866 k N : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) - 1 / (2 : ℝ) ^ k) :=
  sorry

/--
Erdős Problem #866, lower bound for large k [CES75]:

For every ε > 0, there exists k₀ such that for all k ≥ k₀,
g_k(N) > N^{1 - ε} for all sufficiently large N.
-/
theorem erdos_problem_866_lower :
    ∀ ε : ℝ, ε > 0 →
    ∃ k₀ : ℕ, ∀ k : ℕ, k ≥ k₀ →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (gPairwiseSum866 k N : ℝ) > (N : ℝ) ^ ((1 : ℝ) - ε) :=
  sorry

end
