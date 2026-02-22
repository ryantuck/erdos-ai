import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open Real

/-!
# Erdős Problem #980

Let $k \geq 2$ and $n_k(p)$ denote the least $k$th power nonresidue of $p$.
Is it true that
  ∑_{p < x} n_k(p) ~ c_k · x / log x
for some constant $c_k > 0$?

Proved by Erdős [Er61e] for k = 2, with c₂ = ∑_{j=1}^∞ p_j / 2^j.
The general case was proved by Elliott [El67b].
-/

/-- `a` is a kth power residue modulo `p` if there exists `b` with `b^k ≡ a (mod p)`. -/
def IsKthPowerResidue (k p a : ℕ) : Prop :=
  ∃ b : ℕ, b ^ k % p = a % p

/-- The least kth power nonresidue of `p`: the smallest positive integer
    that is not a kth power residue modulo `p`. Returns 0 if no such number exists. -/
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  sInf {a : ℕ | 0 < a ∧ ¬IsKthPowerResidue k p a}

/--
Erdős Problem #980 [Er65b]:

For every k ≥ 2, there exists a constant c_k > 0 such that
  ∑_{p < x, p prime} n_k(p) ~ c_k · x / log x.

Formulated as: there exists c_k > 0 such that for every ε > 0, there exists X₀
such that for all x ≥ X₀,
  |∑_{p < x, p prime} n_k(p) - c_k · x / log x| ≤ ε · x / log x.
-/
theorem erdos_problem_980 (k : ℕ) (hk : k ≥ 2) :
    ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ X₀ : ℕ, ∀ x : ℕ, x ≥ X₀ →
      |((Finset.filter (fun p => Nat.Prime p) (Finset.range x)).sum
          (fun p => (leastKthPowerNonresidue k p : ℝ))) -
        c * (x : ℝ) / log (x : ℝ)| ≤
      ε * (x : ℝ) / log (x : ℝ) :=
  sorry

end
