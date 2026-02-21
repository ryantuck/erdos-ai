import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #461

Let $s_t(n)$ be the $t$-smooth component of $n$ — that is, the product of all
primes $p$ (with multiplicity) dividing $n$ such that $p < t$. Let $f(n,t)$
count the number of distinct values of $s_t(m)$ for $m \in [n+1, n+t]$. Is it
true that
$$f(n,t) \gg t$$
uniformly for all $t$ and $n$?

Erdős and Graham report they can show $f(n,t) \gg t / \log t$.
-/

/-- The `t`-smooth component of `n`: the product of `p ^ v_p(n)` over all
    primes `p < t` dividing `n`. -/
def smoothComponent (t n : ℕ) : ℕ :=
  (n.factorization.support.filter (· < t)).prod
    (fun p => p ^ n.factorization p)

/-- `erdos461_f n t` counts the number of distinct values of
    `smoothComponent t m` for `m ∈ {n+1, ..., n+t}`. -/
def erdos461_f (n t : ℕ) : ℕ :=
  ((Finset.Icc (n + 1) (n + t)).image (smoothComponent t)).card

/--
Erdős Problem #461 [ErGr80, p.92]:

Is it true that `f(n,t) ≫ t` uniformly for all `n` and `t`, where `f(n,t)`
counts the number of distinct `t`-smooth components among `{n+1, ..., n+t}`?
-/
theorem erdos_problem_461 :
    ∃ c : ℝ, c > 0 ∧ ∀ n t : ℕ, 0 < t →
      (erdos461_f n t : ℝ) ≥ c * (t : ℝ) :=
  sorry

end
