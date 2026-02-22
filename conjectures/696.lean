import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #696

Let h(n) be the largest ℓ such that there is a sequence of primes
p₁ < ⋯ < p_ℓ all dividing n with p_{i+1} ≡ 1 (mod p_i).

Let H(n) be the largest u such that there is a sequence of integers
d₁ < ⋯ < d_u all dividing n with d_{i+1} ≡ 1 (mod d_i).

Is it true that H(n)/h(n) → ∞ for almost all n?

Reference: [Er79e, p.81]
https://www.erdosproblems.com/696
-/

/-- A list of natural numbers forms a mod-chain: it is strictly increasing
    and consecutive elements satisfy d_{i+1} ≡ 1 (mod d_i). -/
def IsModChain (l : List ℕ) : Prop :=
  List.IsChain (fun a b => a < b ∧ a ∣ (b - 1)) l

/-- h(n): the largest ℓ such that there is a mod-chain of primes of length ℓ
    all dividing n. -/
noncomputable def h_erdos696 (n : ℕ) : ℕ :=
  sSup {k | ∃ l : List ℕ, l.length = k ∧ IsModChain l ∧ ∀ p ∈ l, Nat.Prime p ∧ p ∣ n}

/-- H(n): the largest u such that there is a mod-chain of divisors of length u
    all dividing n. -/
noncomputable def H_erdos696 (n : ℕ) : ℕ :=
  sSup {k | ∃ l : List ℕ, l.length = k ∧ IsModChain l ∧ ∀ d ∈ l, d ∣ n}

/-- Count of integers m ∈ {1, ..., N} satisfying predicate P. -/
noncomputable def countSat696 (P : ℕ → Prop) (N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => P (n + 1))).card

/--
Erdős Problem #696 [Er79e, p.81]:

H(n)/h(n) → ∞ for almost all n.

Formulated as: for every M > 0, the natural density of
{n : H(n) ≥ M · h(n)} is 1.
-/
theorem erdos_problem_696 :
    ∀ M : ℝ, M > 0 →
    Filter.Tendsto
      (fun N : ℕ =>
        (countSat696 (fun n => (H_erdos696 n : ℝ) ≥ M * (h_erdos696 n : ℝ)) (N + 1) : ℝ) /
          ((N + 1 : ℕ) : ℝ))
      atTop (nhds 1) :=
  sorry

end
