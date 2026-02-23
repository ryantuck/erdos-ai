import Mathlib.Data.Set.Function
import Mathlib.Order.Monotone.Basic

namespace Erdos1112

/-- The k-fold sumset of a set S of natural numbers: all sums s₁ + ⋯ + sₖ
    with each sᵢ ∈ S. Defined recursively: 0S = {0}, (k+1)S = {a + b | a ∈ S, b ∈ kS}. -/
def kFoldSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | k + 1, S => {n | ∃ a ∈ S, ∃ b ∈ kFoldSumset k S, n = a + b}

/--
Erdős Problem #1112 (Open) — Erdős and Graham [ErGr80]:

Define r_k(d₁, d₂) to be the smallest integer r (if it exists) such that for any
lacunary sequence B = {b₁ < b₂ < ⋯} of positive integers with b_{i+1} ≥ r·b_i,
there exists a sequence A = {a₁ < a₂ < ⋯} of positive integers with
d₁ ≤ a_{i+1} - a_i ≤ d₂ for all i, and (kA) ∩ B = ∅, where kA is the k-fold sumset.

Known results:
- r₂(2,3) = 2 and r₂(a,b) ≤ 2 for a < b with b ≠ 2a (Erdős–Graham, Chen).
- r₃(2,3) does not exist: Bollobás, Hegyvári, and Jin showed that for any
  arbitrarily fast growing sequence of lacunary ratios, there exists B such
  that (A+A+A) ∩ B ≠ ∅ for all A with gaps in [2,3].
- Further non-existence results by Tang and Yang.
- The general question of existence of r_k(d₁, d₂) for k ≥ 3 remains open.

We state the non-existence direction (consistent with all known results):
for all k ≥ 3 and valid d₁ < d₂, r_k(d₁, d₂) does not exist. That is, for
every lacunary ratio r, there exists a lacunary sequence B with ratio r such
that no gap-bounded sequence A avoids B with its k-fold sumset.

Tags: additive combinatorics
-/
theorem erdos_problem_1112 (d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂)
    (k : ℕ) (hk : 3 ≤ k) (r : ℕ) :
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, r * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, d₁ ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ d₂) →
        ∃ n, n ∈ kFoldSumset k (Set.range A) ∧ n ∈ Set.range B :=
  sorry

end Erdos1112
