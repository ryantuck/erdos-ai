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

**Status: PROVED** — solved in the affirmative (erdosproblems.com/1179 banner:
"This has been solved in the affirmative"; page edition 26 January 2026, archived
capture accessed 2026-02-23; cross-checked against the teorth/erdosproblems
metadata mirror: status "proved", last update 2026-01-26).

It is trivial that g_ε(N) ≥ log₂ N. Erdős and Rényi [ErRe65] proved
g_ε(N) ≤ (2+o(1)) log₂ N + O_ε(1), and Erdős and Hall [ErHa76] improved this to
  g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N.
The Erdős–Hall bound is of the form (1 + o_ε(1)) log₂ N, so together with the
trivial lower bound it answers the "in particular" question affirmatively.

See also Erdős Problem #543 (erdosproblems.com/543), the analogous threshold
problem for subset-sum *completeness* of a random subset.

A problem of Erdős.

[Er73] Erdős, P., *Problems and results on combinatorial number theory*. A survey of
combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins,
Colo., 1971) (1973), 117-138. (Problem source: p. 127.)

[ErRe65] Erdős, P. and Rényi, A., *Probabilistic methods in group theory*.
J. Analyse Math. (1965), 127-138.

[ErHa76] Erdős, P. and Hall, R. R., *Probabilistic methods in group theory. II*.
Houston J. Math. (1976), 173-180.

(Bibliographic data recovered from the original pipeline's archived fetch of
erdosproblems.com/latex/1179 and agreeing sibling files; volume numbers were not
in the recovered extraction and are deliberately omitted, not fabricated.)

**Formalization note (fable-review fix, not compile-verified).** The first-pass
file encoded "with probability → 1 as N → ∞" by the N-coupled threshold
"good fraction ≥ 1 - 1/N", and the resulting limit statement is *false*: for
G = (ℤ/2ℤ)^t of order N = 2^t and any k ≤ (2-η) log₂ N, the probability that a
uniformly random k-subset A is contained in some index-2 subgroup H — which forces
F_A(g) = 0 < (1-ε)·2^k/N for every g ∉ H — is at least on the order of
N·2^(-k) ≥ N^(-(1-η)) ≫ 1/N (Chung–Erdős over the N-1 index-2 subgroups), so the
1 - 1/N threshold forces g(2^t) ≥ (2-o(1))·t along this subsequence and the ratio
g(N)/log₂ N cannot tend to 1. The faithful fixed-confidence reading is used
instead: for every fixed δ ∈ (0,1), the minimal k achieving failure probability
≤ δ in every abelian group of order N is (1 + o_{ε,δ}(1)) log₂ N; the confidence
parameter δ is explicit in `g_eps` below and the main statement quantifies over it.

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
      |F_A(g) - 2^k/N| ≤ ε · 2^k/N  for all g ∈ G.
    (N = Fintype.card G ≥ 1 always, so the divisions are never by zero.) -/
def isApproxUniform {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (A : Finset G) : Prop :=
  let N : ℕ := Fintype.card G
  let k : ℕ := A.card
  ∀ g : G, |((subsetSumCount A g : ℝ) - (2 : ℝ) ^ k / N)| ≤ ε * (2 : ℝ) ^ k / N

/-- The fraction of k-subsets A of a finite abelian group G that are ε-approximation-uniform.
    This models the probability that a uniformly random k-subset satisfies the approximation.
    The division is real-valued; for k > Fintype.card G there are no k-subsets and the
    convention 0/0 = 0 applies — which is desirable: it keeps such k out of the defining
    set of `g_eps` (0 < 1 - δ for δ < 1), matching the implicit constraint k ≤ N. -/
noncomputable def goodFraction {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (ε : ℝ) (k : ℕ) : ℝ :=
  let all := (Finset.univ : Finset G).powersetCard k
  let good := @Finset.filter (Finset G) (fun A => isApproxUniform ε A) (Classical.decPred _) all
  good.card / all.card

/-- `g_eps ε δ N` is the minimal k such that for every finite abelian group G of order N,
    the fraction of k-subsets that are ε-approximation-uniform is at least 1 - δ.
    For each fixed confidence level 1 - δ (0 < δ < 1) this rigorizes the problem's
    "with probability → 1 as N → ∞": the assertion is that the threshold is
    (1 + o(1)) log₂ N for every fixed δ.

    Junk values: `sInf ∅ = 0` on ℕ. The defining set is all of ℕ at N = 0 (no group has
    order 0, so the condition is vacuous) and can be genuinely empty at some small N
    (e.g. N = 3, ε < 1/2, δ < 1/3: exhaustive check shows no k works for ℤ/3ℤ). But for
    all N large enough in terms of ε alone, k = N is in the set: the unique N-subset is
    A = G, and a character-sum computation gives |F_G(g) - 2^N/N| ≤ 2^{N/3} ≤ ε·2^N/N
    for every abelian G of order N (nontrivial characters of even order contribute 0 and
    of odd order m ≥ 3 contribute 2^{N/m} ≤ 2^{N/3}), so the fraction is 1. Hence the
    junk value occurs at only finitely many N and is invisible to the atTop limit. -/
noncomputable def g_eps (ε δ : ℝ) (N : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [hG : AddCommGroup G] [hF : Fintype G] [hD : DecidableEq G],
    Fintype.card G = N →
    @goodFraction G hG hF hD ε k ≥ 1 - δ}

/--
Erdős Problem #1179 [Er73, p.127] — PROVED (solved in the affirmative):

For all 0 < ε < 1 and every fixed confidence parameter 0 < δ < 1,
  g_{ε,δ}(N) = (1 + o_{ε,δ}(1)) log₂ N as N → ∞, i.e.,
  g_{ε,δ}(N) / log₂ N → 1  as N → ∞.

Here g_{ε,δ}(N) is the minimal k such that for every abelian group G of order N,
at least a (1 - δ) fraction of all k-subsets A of G satisfy
  |F_A(g) - 2^k/N| ≤ ε · 2^k/N  for all g ∈ G,
where F_A(g) = #{S ⊆ A : Σ_{x∈S} x = g}. Quantifying over all fixed δ ∈ (0,1) is
the faithful rendering of the problem's "with probability → 1 as N → ∞" (the
earlier N-coupled threshold 1 - 1/N makes the statement false along N = 2^t;
see the module docstring).

The lower bound g_{ε,δ}(N) ≥ log₂ N is trivial (for all large N).
Erdős and Rényi [ErRe65] proved g_ε(N) ≤ (2 + o(1)) log₂ N + O_ε(1).
Erdős and Hall [ErHa76] proved g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N,
which resolves this problem in the affirmative.
-/
theorem erdos_problem_1179 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    Tendsto (fun N : ℕ => (g_eps ε δ N : ℝ) / logb 2 N)
      atTop (nhds 1) :=
  sorry

/--
Trivial lower bound (page remark, source-verified): g_ε(N) ≥ log₂ N. In the
fixed-confidence formalization: for all large N, g_{ε,δ}(N) ≥ log₂ N. Stated in
eventual form because at the finitely many N where the defining set of `g_eps` is
empty the junk value 0 violates the pointwise bound. (For any k in the defining
set and any G of order N ≥ 1, a fraction ≥ 1 - δ > 0 of k-subsets are
ε-approximation-uniform, so some ε-uniform A exists; then every g ∈ G has
F_A(g) ≥ (1-ε)·2^k/N > 0, so all N elements are subset sums of A, forcing
2^k ≥ N.)
-/
theorem erdos_problem_1179.variants.trivial_lower_bound
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, logb 2 N ≤ (g_eps ε δ N : ℝ) :=
  sorry

/--
Erdős and Rényi [ErRe65] (page remark, source-verified): for all 0 < ε < 1,
  g_ε(N) ≤ (2 + o(1)) log₂ N + O_ε(1).
In the fixed-confidence formalization, the O_ε(1) term is absorbed: for every
γ > 0, eventually g_{ε,δ}(N) ≤ (2 + γ) log₂ N.
-/
theorem erdos_problem_1179.variants.erdos_renyi_upper
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (g_eps ε δ N : ℝ) ≤ (2 + γ) * logb 2 N :=
  sorry

/--
Erdős and Hall [ErHa76] (page remark, source-verified): for all 0 < ε < 1,
  g_ε(N) ≤ (1 + O_ε(log log log N / log log N)) log₂ N.
Stated with natural logarithms in the correction factor (the ratio
log log log N / log log N is base-invariant up to a constant absorbed in C) and in
eventual form so that N₀ absorbs the small N where the iterated logarithms are
non-positive (Lean's Real.log junk values). This bound implies the main statement.
-/
theorem erdos_problem_1179.variants.erdos_hall_upper
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (g_eps ε δ N : ℝ) ≤
        (1 + C * (log (log (log (N : ℝ))) / log (log (N : ℝ)))) * logb 2 N :=
  sorry

end Erdos1179

end
