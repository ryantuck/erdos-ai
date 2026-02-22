import Mathlib.Data.Nat.Lattice

/-!
# Erdős Problem #966

Let k, r ≥ 2. Does there exist a set A ⊆ ℕ that contains no non-trivial
arithmetic progression of length k + 1, yet in any r-colouring of A there
must exist a monochromatic non-trivial arithmetic progression of length k?

A problem of Erdős [Er75b]. Spencer has shown that such a set exists.
This is an arithmetic analogue of the graph theory version [924].
-/

/--
Erdős Problem #966 [Er75b]:

For all k ≥ 2 and r ≥ 2, there exists a set A ⊆ ℕ that contains no
(k+1)-term arithmetic progression, yet every r-colouring of A contains
a monochromatic k-term arithmetic progression.

Proved by Spencer.
-/
theorem erdos_problem_966 (k : ℕ) (r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    ∃ (A : Set ℕ),
      (¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k + 1 → a + i * d ∈ A) ∧
      (∀ c : ℕ → Fin r,
        ∃ a d : ℕ, 0 < d ∧
          (∀ i : ℕ, i < k → a + i * d ∈ A) ∧
          ∀ i : ℕ, i < k → c (a + i * d) = c a) :=
  sorry
