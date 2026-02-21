import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset Filter

noncomputable section

/-!
# Erdős Problem #530

Let ℓ(N) be maximal such that in any finite set A ⊂ ℝ of size N there exists
a Sidon subset S of size ℓ(N) (i.e. the only solutions to a + b = c + d in S
are the trivial ones). Is it true that ℓ(N) ~ N^{1/2}?

Originally asked by Riddell [Ri69]. Erdős noted the bounds
  N^{1/3} ≪ ℓ(N) ≤ (1+o(1))N^{1/2}
(the upper bound following from the case A = {1,…,N}). The lower bound was
improved to N^{1/2} ≪ ℓ(N) by Komlós, Sulyok, and Szemerédi [KSS75]. The
correct constant is unknown, but it is likely that the upper bound is true,
so that ℓ(N) ~ N^{1/2}.
-/

/-- A Finset of real numbers is a Sidon set if for all a, b, c, d in the set
    with a + b = c + d, we have {a, b} = {c, d} (i.e., all pairwise sums
    are distinct). -/
def IsSidonSet (S : Finset ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The maximum size of a Sidon subset of A. -/
noncomputable def maxSidonSubsetSize (A : Finset ℝ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℝ, S ⊆ A ∧ IsSidonSet S ∧ S.card = k}

/-- ℓ(N): the largest k such that every N-element subset of ℝ contains a Sidon
    subset of size at least k. Equivalently, the minimum of maxSidonSubsetSize A
    over all N-element sets A ⊂ ℝ. -/
noncomputable def sidonSubsetNumber (N : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ A : Finset ℝ, A.card = N ∧ maxSidonSubsetSize A = m}

/--
Erdős Conjecture (Problem #530) [Er73,p.120][Er75f,p.104][Er80e]:

ℓ(N) ~ N^{1/2}, i.e. the ratio ℓ(N) / √N tends to 1 as N → ∞.

Known bounds: N^{1/2} ≪ ℓ(N) ≤ (1+o(1))N^{1/2}. The lower bound N^{1/2} ≪ ℓ(N)
is due to Komlós, Sulyok, and Szemerédi [KSS75]. The upper bound follows from
the case A = {1,…,N}.
-/
theorem erdos_problem_530 :
    Tendsto (fun N : ℕ => (sidonSubsetNumber N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds 1) :=
  sorry

end
