import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Order.Basic

open Filter Real Finset

noncomputable section

/-!
# Erdős Problem #478

Let $p$ be a prime and $A_p = \{ k! \pmod{p} : 1 \leq k < p \}$.
Is it true that $|A_p| \sim (1 - 1/e) \cdot p$?

That is, as $p \to \infty$ through the primes, the number of distinct
factorial residues modulo $p$ is asymptotically $(1 - 1/e) \cdot p$.

The best known lower bound is $|A_p| \geq (\sqrt{2} - o(1)) p^{1/2}$
due to Grebennikov, Sagdeev, Semchankau, and Vasilevskii [GSSV24].
Wilson's theorem gives the upper bound $|A_p| \leq p - 2$.
-/

/-- The set of distinct factorial residues modulo p:
    A_p = { k! mod p : 1 ≤ k < p }. -/
def factorialResidues (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (p - 1)).image (fun k => Nat.factorial k % p)

/--
Erdős Problem #478 [ErGr80, p.96]:

Let p be a prime and A_p = { k! mod p : 1 ≤ k < p }.
Is it true that |A_p| ~ (1 - 1/e) · p?

Formally: the ratio |A_p| / ((1 - e⁻¹) · p) tends to 1 as p → ∞
through the primes.
-/
theorem erdos_problem_478 :
    Tendsto
      (fun p : ℕ =>
        (factorialResidues p).card / ((1 - Real.exp (-1)) * (p : ℝ)))
      (atTop ⊓ Filter.principal {p | Nat.Prime p})
      (nhds 1) :=
  sorry

end
