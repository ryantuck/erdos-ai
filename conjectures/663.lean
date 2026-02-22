import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #663

Let k ≥ 2 and q(n, k) denote the least prime which does not divide
∏_{1 ≤ i ≤ k} (n + i). Is it true that, if k is fixed and n is
sufficiently large, we have q(n, k) < (1 + o(1)) log n?

A problem of Erdős and Pomerance [BEGL96][Er97e].

The bound q(n, k) < (1 + o(1)) k log n is easy. It may be true that this
improved bound holds even up to k = o(log n).

See also problem [457].
-/

/-- q(n, k) is the least prime which does not divide ∏_{i=1}^{k} (n + i).
    Returns 0 if no such prime exists (which cannot happen since a finite
    product has only finitely many prime factors). -/
noncomputable def leastNondividingPrime (n k : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ¬(p ∣ ∏ i ∈ Finset.range k, (n + i + 1))}

/--
Erdős Problem #663 [BEGL96][Er97e]:

For any fixed k ≥ 2, q(n, k) < (1 + o(1)) log n as n → ∞,
where q(n, k) is the least prime not dividing ∏_{i=1}^{k} (n + i).

Formulated as: for every ε > 0, there exists N₀ such that for all n ≥ N₀,
  q(n, k) < (1 + ε) · log n.
-/
theorem erdos_problem_663 (k : ℕ) (hk : k ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (leastNondividingPrime n k : ℝ) < (1 + ε) * Real.log (n : ℝ) :=
  sorry

end
