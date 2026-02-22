import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Defs

open Finset BigOperators Complex

noncomputable section

/-!
# Erdős Problem #974

Let z_1, ..., z_n ∈ ℂ be a sequence such that z_1 = 1. Suppose that the
power sums s_k = ∑_{i=1}^{n} z_i^k contain infinitely many (n-1)-tuples
of consecutive values which are all 0. Then (essentially) z_j = e^{2πij/n},
i.e., the z_j are the n-th roots of unity.

A conjecture of Turán, proved by Tijdeman [Ti66] in the stronger form
requiring only two such (n-1)-tuples.
-/

/--
Erdős Problem #974 (Turán's conjecture, proved by Tijdeman):

If z : Fin n → ℂ with z 0 = 1, and there are infinitely many k ∈ ℕ such that
the n - 1 consecutive power sums s_k, s_{k+1}, ..., s_{k+n-2} are all zero,
then the z_i are a permutation of the n-th roots of unity e^{2πij/n}.
-/
theorem erdos_problem_974 {n : ℕ} (hn : 2 ≤ n)
    (z : Fin n → ℂ)
    (hz1 : z ⟨0, by omega⟩ = 1)
    (hzeros : ∀ N : ℕ, ∃ k ≥ N, ∀ j : ℕ, j < n - 1 →
      (∑ i : Fin n, (z i) ^ (k + j)) = 0) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
      z (σ i) = exp (2 * ↑Real.pi * I * ↑(i.val) / ↑n) :=
  sorry

end
