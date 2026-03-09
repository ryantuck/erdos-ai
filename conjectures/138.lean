import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter Real Classical

/--
A monochromatic k-term arithmetic progression exists in a 2-coloring c of
{0, …, N-1}: there exist a, d with d > 0 such that a, a+d, …, a+(k-1)d are
all in {0, …, N-1} and all receive the same color.
-/
def HasMonoArithProg (c : ℕ → Bool) (N k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ∀ i : ℕ, i < k → c (a + i * d) = c a

/--
The van der Waerden property: N is large enough that every 2-coloring of
{0, …, N-1} contains a monochromatic k-term arithmetic progression.
-/
def VanDerWaerdenProp (k N : ℕ) : Prop :=
  ∀ c : ℕ → Bool, HasMonoArithProg c N k

/--
Van der Waerden's theorem states that for every k ≥ 1, there exists N such that
VanDerWaerdenProp k N holds. We axiomatize this classical result.
-/
axiom vanDerWaerden (k : ℕ) : ∃ N : ℕ, VanDerWaerdenProp k N

/--
The van der Waerden number W(k): the smallest N such that every 2-coloring
of {0, …, N-1} contains a monochromatic k-term arithmetic progression.
-/
noncomputable def W (k : ℕ) : ℕ :=
  Nat.find (vanDerWaerden k)

/--
Erdős Problem #138 [Er57, Er61, Er73, Er74b, Er75b, Er77c, ErGr79, Er80, ErGr80, Er81, Er97c]:

Let W(k) be the van der Waerden number, the smallest N such that every
2-coloring of {1, …, N} contains a monochromatic k-term arithmetic progression.
Prove that W(k)^{1/k} → ∞ as k → ∞.

Erdős offered $500 for a proof or disproof. The best known upper bound is a
tower of exponentials due to Gowers (2001), while the best lower bound is
W(k) ≫ 2^k due to Kozik and Shabanov (2016).
-/
theorem erdos_problem_138 :
    Tendsto (fun k => (W k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop atTop :=
  sorry
