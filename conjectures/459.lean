import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #459

Let $f(u)$ be the largest $v$ such that no $m \in (u,v)$ is composed entirely
of primes dividing $uv$. Equivalently, $f(u)$ is the smallest integer $v > u$
such that every prime factor of $v$ divides $u$.

Trivially $u + 2 \leq f(u) \leq u^2$.

Cambie showed:
- $f(p) = p^2$ for every prime $p$
- $f(u) = u + 2$ whenever $u = 2^k - 2$ for $k \geq 2$
- $f(n) = (1 + o(1))n$ for almost all $n$

This problem is marked as solved.
-/

/-- `erdos459_f u` is the smallest `v > u` such that every prime factor
    of `v` divides `u`. -/
noncomputable def erdos459_f (u : ℕ) : ℕ :=
  sInf {v : ℕ | u < v ∧ ∀ p : ℕ, Nat.Prime p → p ∣ v → p ∣ u}

/--
Erdős Problem #459 (Lower bound) [ErGr80, p.91]:

For all u ≥ 2, f(u) ≥ u + 2.
-/
theorem erdos_problem_459_lower_bound (u : ℕ) (hu : 2 ≤ u) :
    u + 2 ≤ erdos459_f u :=
  sorry

/--
Erdős Problem #459 (Upper bound) [ErGr80, p.91]:

For all u ≥ 2, f(u) ≤ u².
-/
theorem erdos_problem_459_upper_bound (u : ℕ) (hu : 2 ≤ u) :
    erdos459_f u ≤ u ^ 2 :=
  sorry

/--
Erdős Problem #459 (Prime case, Cambie):

For every prime p, f(p) = p².
-/
theorem erdos_problem_459_prime (p : ℕ) (hp : Nat.Prime p) :
    erdos459_f p = p ^ 2 :=
  sorry

/--
Erdős Problem #459 (Almost all, Cambie):

f(n) = (1 + o(1))n for almost all n, i.e., for every ε > 0, the density
of {n : f(n) > (1 + ε)n} tends to 0.
-/
theorem erdos_problem_459_almost_all (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        (erdos459_f n : ℝ) > (1 + ε) * (n : ℝ))).card : ℝ) / (x : ℝ))
      atTop (nhds 0) :=
  sorry

end
