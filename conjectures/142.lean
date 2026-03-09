import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter

/--
A Finset S of natural numbers is free of non-trivial k-term arithmetic
progressions: there do not exist a, d with d ≥ 1 such that
{a, a+d, …, a+(k-1)d} ⊆ S.
-/
def APFree (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ∃ i : ℕ, i < k ∧ a + i * d ∉ S

/--
r_k(N) is the largest size of a subset of {0, …, N-1} with no non-trivial
k-term arithmetic progression.
-/
noncomputable def rk (k N : ℕ) : ℕ :=
  sSup ((fun S => S.card) '' {S : Finset ℕ | S ⊆ Finset.range N ∧ APFree k S})

/--
Erdős Problem #142 [Er80, Er81, Er97c]:

Let r_k(N) be the largest possible size of a subset of {1,…,N} that does not
contain any non-trivial k-term arithmetic progression. Prove an asymptotic
formula for r_k(N).

More precisely: for each k ≥ 3, there exists a function f : ℕ → ℝ such that
r_k(N) / f(N) → 1 as N → ∞.

Erdős called this 'probably unattackable at present' and offered $10000 for a
proof. An asymptotic formula is still far out of reach, even for k = 3.
-/
theorem erdos_problem_142 (k : ℕ) (hk : 3 ≤ k) :
    ∃ f : ℕ → ℝ, (∀ᶠ N in atTop, 0 < f N) ∧
      Tendsto (fun N => (rk k N : ℝ) / f N) atTop (nhds 1) :=
  sorry
