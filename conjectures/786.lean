import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped Classical
open Finset

/--
A set A ⊆ ℕ is **product-length determining** if whenever a₁⋯aᵣ = b₁⋯bₛ
with all aᵢ, bⱼ ∈ A, then r = s. That is, equal products from elements of A
must use the same number of factors.
-/
def ProductLengthDetermining (A : Set ℕ) : Prop :=
  ∀ (as bs : List ℕ),
    (∀ a ∈ as, a ∈ A) →
    (∀ b ∈ bs, b ∈ A) →
    as.prod = bs.prod →
    as.length = bs.length

/--
A set A ⊆ ℕ has **upper density at least d** if for every ε > 0,
eventually the count of elements of A in {1,…,N} is at least (d - ε) · N.
-/
def HasUpperDensityAtLeast (A : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card ≥ (d - ε) * (N : ℝ)

/--
Erdős Problem #786 [Er65, Er69 p.81, Er73 p.132]:

Let ε > 0. Is there some set A ⊂ ℕ of density > 1 - ε such that
a₁⋯aᵣ = b₁⋯bₛ with aᵢ, bⱼ ∈ A can only hold when r = s?

An example of such a set with density 1/4 is given by the integers ≡ 2 (mod 4).
Selfridge constructed such a set with density 1/e - ε for any ε > 0.
A result of Erdős, Ruzsa, and Sárközy implies the density is at most 1/2.
-/
theorem erdos_problem_786a :
    ∀ ε : ℝ, 0 < ε →
      ∃ A : Set ℕ,
        ProductLengthDetermining A ∧
        HasUpperDensityAtLeast A (1 - ε) :=
  sorry

/--
Erdős Problem #786 (finite version):

Can one always find a set A ⊆ {1,…,N} that is product-length determining
and has size ≥ (1 - o(1)) · N? That is, for every ε > 0 and all
sufficiently large N, there exists such an A with |A| ≥ (1 - ε) · N.
-/
theorem erdos_problem_786b :
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∃ A : Finset ℕ,
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
          ProductLengthDetermining (↑A : Set ℕ) ∧
          (A.card : ℝ) ≥ (1 - ε) * (N : ℝ) :=
  sorry
