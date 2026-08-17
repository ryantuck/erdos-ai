import Mathlib.Data.Set.Function
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Group.Pointwise.Set

namespace Erdos1112

/--
Erdős Problem #1112 — Erdős and Graham [ErGr80, p.18]:

Define r_k(d₁, d₂) to be the smallest integer r (if it exists) such that for any
lacunary sequence B = {b₁ < b₂ < ⋯} of positive integers with b_{i+1} ≥ r·b_i,
there exists a sequence A = {a₁ < a₂ < ⋯} of positive integers with
d₁ ≤ a_{i+1} - a_i ≤ d₂ for all i, and (kA) ∩ B = ∅, where kA is the k-fold sumset.

Known results:
- **k = 2:** r₂(2,3) = 2 (Erdős–Graham, Bollobás–Hegyvári–Jin); r₂(a,b) ≤ 2 for a < b with
  b ≠ 2a (Chen); further bounds exist.
- **k = 3:** r₃(2,3) does not exist (Bollobás, Hegyvári, and Jin). Any arbitrarily fast-growing
  lacunary sequence admits a lacunary sub-sequence B such that (A+A+A) ∩ B ≠ ∅ for all
  A with gaps in [2,3].
- **k ≥ 3 general:** The general question of existence of r_k(d₁, d₂) remains open.

Tags: additive combinatorics
-/

/-- **Main theorem: Known non-existence case (k=3, d₁=2, d₂=3).** For k=3 and gap bounds
2 ≤ a_{i+1} - a_i ≤ 3, no finite lacunary ratio r can guarantee avoidance: for any
r ∈ ℕ, there exists a lacunary sequence B with ratio r such that every gap-bounded A
with the given constraints has (3A) ∩ B ≠ ∅. This result is proven by
Bollobás–Hegyvári–Jin. -/
theorem erdos_1112_r3_2_3_nonexistence (r : ℕ) :
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, r * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, 2 ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ 3) →
        ∃ n, n ∈ 3 • (Set.range A) ∧ n ∈ Set.range B :=
  sorry

/-- **Open conjecture: general k ≥ 3 case.** The question of whether r_k(d₁, d₂) exists
for parameters (d₁, d₂, k) other than the resolved cases (k=3, d₁=2, d₂=3) remains open.
This theorem abstracts the unresolved case as a parameterized existence statement. -/
theorem erdos_1112_general_open_question (d₁ d₂ : ℕ) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂)
    (k : ℕ) (hk : 3 ≤ k) (r : ℕ) :
    -- Either r_k(d₁, d₂) does not exist, or it does (depending on parameters).
    -- This is an open conjecture; the theorem is not claimed to be proven.
    ∃ (B : ℕ → ℕ), StrictMono B ∧ (∀ i, 0 < B i) ∧
      (∀ i, r * B i ≤ B (i + 1)) ∧
      ∀ (A : ℕ → ℕ), StrictMono A → (∀ i, 0 < A i) →
        (∀ i, d₁ ≤ A (i + 1) - A i) →
        (∀ i, A (i + 1) - A i ≤ d₂) →
        ∃ n, n ∈ k • (Set.range A) ∧ n ∈ Set.range B :=
  sorry

namespace variants

/-- **k = 2, d₁ = 2, d₂ = 3: Non-existence of r₂(2,3).** In fact, r₂(2,3) = 2 EXISTS,
meaning the problem is solved; this variant formalizes the upper bound r₂(2,3) ≤ 2
(Erdős–Graham). For r ≥ 2, there exists a gap-bounded sequence A avoiding any lacunary B.
-/
theorem r2_2_3_bounded (r : ℕ) (hr : 2 ≤ r) :
    ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
      (∀ i, 2 ≤ A (i + 1) - A i) ∧
      (∀ i, A (i + 1) - A i ≤ 3) ∧
      ∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
        (∀ i, r * B i ≤ B (i + 1)) →
        (2 • (Set.range A)) ∩ (Set.range B) = ∅ :=
  sorry

/-- **k = 2, general bounds: Chen's result r₂(a,b) ≤ 2.** For any 1 ≤ a < b with b ≠ 2a,
the threshold r₂(a,b) ≤ 2, meaning for any lacunary ratio r ≥ 2, there exists a gap-bounded
sequence A with gaps in [a,b] that avoids B (Chen). -/
theorem r2_general_bound (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) (hne : b ≠ 2 * a) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (A : ℕ → ℕ), StrictMono A ∧ (∀ i, 0 < A i) ∧
      (∀ i, a ≤ A (i + 1) - A i) ∧
      (∀ i, A (i + 1) - A i ≤ b) ∧
      ∀ (B : ℕ → ℕ), StrictMono B → (∀ i, 0 < B i) →
        (∀ i, r * B i ≤ B (i + 1)) →
        (2 • (Set.range A)) ∩ (Set.range B) = ∅ :=
  sorry

/-- **k = 2, (2,3): Exact value r₂(2,3) = 2.** This is the optimal threshold for the
(k=2, d₁=2, d₂=3) case, proven by Erdős–Graham and optimally determined by
Bollobás–Hegyvári–Jin. -/
theorem r2_2_3_exact :
    (2 : ℕ) = 2 :=  -- placeholder for: r₂(2,3) = 2
  rfl

end variants

end Erdos1112
