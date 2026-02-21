import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Squarefree.Basic

/-!
# Erdős Problem #175

Show that, for any n ≥ 5, the binomial coefficient C(2n, n) is not squarefree.

It is easy to see that 4 ∣ C(2n, n) except when n = 2^k, and hence it suffices
to prove this when n is a power of 2.

Proved by Sárközy [Sa85] for all sufficiently large n, and independently by
Granville and Ramaré [GrRa96] and Velammal [Ve95] for all n ≥ 5.
-/

/--
Erdős Problem #175 [Er79, ErGr80]:
For any n ≥ 5, the central binomial coefficient C(2n, n) is not squarefree.
That is, there exists some prime p such that p² divides C(2n, n).
-/
theorem erdos_problem_175 :
    ∀ n : ℕ, 5 ≤ n → ¬Squarefree (Nat.choose (2 * n) n) :=
  sorry
