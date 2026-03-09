import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

open Nat Filter Real

namespace Erdos1101

/--
A pairwise coprime sequence of integers ≥ 2 with convergent reciprocal sum.
We model this as a function `u : ℕ → ℕ` where `u` is strictly increasing,
all values are ≥ 2, pairwise coprime, and ∑ 1/u(i) converges.
-/
structure GoodSeqData where
  u : ℕ → ℕ
  strictMono : StrictMono u
  ge_two : ∀ i, 2 ≤ u i
  pairwiseCoprime : ∀ i j, i ≠ j → Nat.Coprime (u i) (u j)
  summable_recip : Summable (fun i => (1 : ℝ) / (u i : ℝ))

/--
The "sifted" set: integers not divisible by any u(i).
-/
def siftedSet (ud : GoodSeqData) : Set ℤ :=
  {a : ℤ | 0 < a ∧ ∀ i, ¬((ud.u i : ℤ) ∣ a)}

/--
The partial product u(0) * u(1) * ... * u(n-1).
-/
def partialProd (ud : GoodSeqData) : ℕ → ℕ
  | 0 => 1
  | n + 1 => partialProd ud n * ud.u n

/--
The partial products of a sequence with all terms ≥ 2 grow without bound.
-/
theorem partialProd_unbounded (ud : GoodSeqData) (x : ℕ) :
    ∃ n, x < partialProd ud n := by
  induction x with
  | zero => exact ⟨1, by simp [partialProd]; linarith [ud.ge_two 0]⟩
  | succ x ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by
      unfold partialProd
      have h2 := ud.ge_two n
      nlinarith⟩

/--
t_x is the largest t such that u(0)*...*u(t-1) ≤ x.
-/
noncomputable def tOfX (ud : GoodSeqData) (x : ℕ) : ℕ :=
  Nat.find (partialProd_unbounded ud x) - 1

/--
The max gap among sifted integers below x.
-/
noncomputable def maxGap (ud : GoodSeqData) (x : ℕ) : ℕ :=
  sSup {g : ℕ | ∃ a ∈ siftedSet ud, ∃ b ∈ siftedSet ud,
    a < b ∧ b ≤ (x : ℤ) ∧ g = (b - a).toNat ∧
    ∀ c ∈ siftedSet ud, a < c → c < b → False}

/--
The infinite product ∏(1 - 1/u(i))⁻¹, i.e., ∏ u(i)/(u(i)-1).
We define the partial products and take their supremum.
-/
noncomputable def inverseProd (ud : GoodSeqData) : ℝ :=
  ⨆ n, ∏ i ∈ Finset.range n, ((ud.u i : ℝ) / ((ud.u i : ℝ) - 1))

/--
A sequence is "good" if for all ε > 0, for sufficiently large x,
the maximum gap among sifted integers below x is
< (1 + ε) * t_x * ∏(1 - 1/u_i)⁻¹.
-/
def IsGoodSeq (ud : GoodSeqData) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (x : ℕ) in atTop,
    (maxGap ud x : ℝ) < (1 + ε) * (tOfX ud x : ℝ) * inverseProd ud

/-- Erdős Problem #1101, Question 1 (OPEN) [Er81h]:

Is there a good sequence u such that u(n) < n^{O(1)}?

Erdős believed the answer is NO: there is no good sequence with
polynomial growth. That is, for every C > 0 and every good sequence,
u(n) > n^C for infinitely many n. -/
theorem erdos_1101_no_polynomial_good_seq :
    ∀ ud : GoodSeqData, IsGoodSeq ud →
      ∀ C : ℝ, 0 < C → ∃ᶠ (n : ℕ) in atTop, (n : ℝ) ^ C < (ud.u n : ℝ) :=
  sorry

/-- Erdős Problem #1101, Question 2 (OPEN) [Er81h]:

Is there a good sequence u such that u(n) ≤ e^{o(n)}?

Erdős believed the answer is YES. That is, there exists a good sequence
such that log(u(n))/n → 0. -/
theorem erdos_1101_subexponential_good_seq :
    ∃ ud : GoodSeqData, IsGoodSeq ud ∧
      Tendsto (fun n => Real.log (ud.u n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
  sorry

end Erdos1101
