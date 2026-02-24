import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Basic

open Filter Real

noncomputable section

namespace Erdos1179

/-!
# Erdős Problem #1179

Let 0 < ε < 1 and let g_ε(N) be the minimal k such that if G is an abelian group
of size N and A ⊆ G is a uniformly random subset of size k, and
  F_A(g) = #{S ⊆ A : g = Σ_{x∈S} x},
then, with probability → 1 as N → ∞,
  |F_A(g) - 2^k/N| ≤ ε · 2^k/N
for all g ∈ G. Estimate g_ε(N); in particular, is it true that for all ε > 0,
  g_ε(N) = (1 + o_ε(1)) log₂ N?

It is trivial that g_ε(N) ≥ log₂ N. Erdős and Rényi proved g_ε(N) ≤ (2+o(1)) log₂ N + O_ε(1),
and Erdős and Hall improved this to
  g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N.

A problem of Erdős.

Tags: additive combinatorics, probability
-/

/-- For a finite abelian group G, a subset A ⊆ G, and element g ∈ G,
    F_A(g) = #{S ⊆ A : Σ_{x∈S} x = g} counts the subsets of A (including ∅)
    whose element-sum equals g. -/
def subsetSumCount {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (g : G) : ℕ :=
  (A.powerset.filter (fun S => S.sum id = g)).card

/-- A k-subset A of a finite abelian group G of size N is ε-approximation-uniform if
    the subset-sum counts are uniformly close to their "expected" value 2^k/N:
      |F_A(g) - 2^k/N| ≤ ε · 2^k/N  for all g ∈ G. -/
def isApproxUniform {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (A : Finset G) : Prop :=
  let N : ℕ := Fintype.card G
  let k : ℕ := A.card
  ∀ g : G, |((subsetSumCount A g : ℝ) - (2 : ℝ) ^ k / N)| ≤ ε * (2 : ℝ) ^ k / N

/-- The fraction of k-subsets A of a finite abelian group G that are ε-approximation-uniform.
    This models the probability that a uniformly random k-subset satisfies the approximation. -/
noncomputable def goodFraction {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (k : ℕ) : ℝ :=
  let all := (Finset.univ : Finset G).powersetCard k
  let good := @Finset.filter (Finset G) (fun A => isApproxUniform ε A) (Classical.decPred _) all
  good.card / all.card

/-- g_ε(N) is the minimal k such that for every finite abelian group G of order N,
    the fraction of k-subsets that are ε-approximation-uniform is at least 1 - 1/N.
    This captures the condition "with probability → 1 as N → ∞" for each N. -/
noncomputable def g_eps (ε : ℝ) (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [hG : AddCommGroup G] [hF : Fintype G] [hD : DecidableEq G],
    Fintype.card G = N →
    @goodFraction G hG hF hD ε k ≥ 1 - 1 / (N : ℝ)}

/--
Erdős Problem #1179 [Er73, p.127]:

For all 0 < ε < 1, g_ε(N) = (1 + o_ε(1)) log₂ N as N → ∞, i.e.,
  g_ε(N) / log₂ N → 1  as N → ∞.

Here g_ε(N) is the minimal k such that for every abelian group G of order N,
at least a (1 - 1/N) fraction of all k-subsets A of G satisfy
  |F_A(g) - 2^k/N| ≤ ε · 2^k/N  for all g ∈ G,
where F_A(g) = #{S ⊆ A : Σ_{x∈S} x = g}.

The lower bound g_ε(N) ≥ log₂ N is trivial.
Erdős and Rényi proved g_ε(N) ≤ (2 + o(1)) log₂ N + O_ε(1).
Erdős and Hall proved g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N.
-/
theorem erdos_problem_1179 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    Filter.Tendsto (fun N : ℕ => (g_eps ε N : ℝ) / Real.logb 2 N)
      Filter.atTop (nhds 1) :=
  sorry

end Erdos1179

end
