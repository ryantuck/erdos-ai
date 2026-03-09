import Mathlib.Data.Set.Function
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Cofinite

open Set

/--
A set A ⊆ ℕ is a **Sidon set** (or B₂ set) if all pairwise sums are distinct:
for a, b, c, d ∈ A with a ≤ b and c ≤ d, a + b = c + d implies a = c and b = d.
-/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → a ≤ b → c ≤ d → a = c ∧ b = d

/--
The complement of A contains an **infinite arithmetic progression**: there exist
a ≥ 0 and d ≥ 1 such that a + n * d ∉ A for all n ∈ ℕ.
-/
def ComplementContainsInfiniteAP (A : Set ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ n : ℕ, a + n * d ∉ A

/--
Erdős Problem #198 [ErGr79, ErGr80]:

If A ⊂ ℕ is a Sidon set then must the complement of A contain an infinite
arithmetic progression?

The answer is **no** (DISPROVED). Erdős and Graham report this was proved by
Baumgartner [Ba75]. A simple construction: enumerate all infinite arithmetic
progressions P₁, P₂, … and greedily choose aₙ ∈ Pₙ with aₙ > 2aₙ₋₁. The
resulting lacunary set is Sidon and hits every infinite AP.

AlphaProof gave the explicit construction A = {(n+1)! + n : n ≥ 0}, which is
Sidon and intersects every infinite arithmetic progression.
-/
theorem erdos_problem_198 :
    ¬ (∀ A : Set ℕ, Set.Infinite A → IsSidonSet A →
      ComplementContainsInfiniteAP A) :=
  sorry
