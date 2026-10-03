-- [AI - Claude Opus 5.5]: Erdős Problem 117 — second-pass formalization
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #117: Covering Groups with Few Pairwise Non-commuting Elements

*Source:* [erdosproblems.com/117](https://www.erdosproblems.com/117) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the tidied
problem box). [Er90] [Er97f] [Va99, 5.75]

Let $h(n)$ be minimal such that any group $G$ with the property that any subset of $>n$
elements contains some $x\neq y$ such that $xy=yx$ can be covered by at most $h(n)$ many
Abelian subgroups.

Estimate $h(n)$ as well as possible.

Remarks recorded on the page:
* Pyber [Py87] has proved there exist constants $c_2>c_1>1$ such that $c_1^n<h(n)<c_2^n$.
  Erdős [Er97f] writes that the lower bound was already known to Isaacs.

**Status of the formal statements.** "Estimate $h(n)$ as well as possible" has no single
formal target. `erdos_problem_117` records the PROVED estimate of Pyber, the best one
recorded on the page.

**Small $n$.** The exponential bounds hold only for large $n$. If every two distinct elements
commute, the group is abelian, so $h(1) = 1$. In any non-abelian group, non-commuting $x, y$
give three pairwise non-commuting elements $x, y, xy$, so $h(2) = 1$ as well. Hence
$c_1^n < h(n)$ with $c_1 > 1$ fails at $n = 1, 2$. The first pass asserted it for every
$n \ge 1$, which is false; see `erdos_problem_117.variants.first_pass_false`.

**Encoding.** All groups are allowed, as on the page, including infinite ones. A group with
the property is centre-by-finite, by a theorem of Neumann. `erdosH 0 = 0`, because no group
satisfies the property with $n = 0$ (a singleton has no two distinct elements), so every $k$
qualifies vacuously.

Tags: group theory.

## References

* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. (Problem 5.75.)
* [Py87] Pyber, L., _The number of pairwise noncommuting elements and the index of the centre
  in a finite group_. J. London Math. Soc. (2) (1987), 287–295.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/117` for [Er97f] and
[Py87]. Sibling `/latex` extractions for [Er90] and [Va99].)
-/

/-- A group G satisfies the n-commuting property if every finite subset of size
    greater than n contains two distinct elements x ≠ y with xy = yx. -/
def HasNCommutingProperty (n : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ (S : Finset G), n < S.card →
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ x * y = y * x

/-- A group G can be covered by at most k Abelian subgroups: there exist k subgroups
    H₀, …, Hₖ₋₁ (possibly with repetition), each of which is abelian, whose union
    is all of G. -/
def CoveredByAbelianSubgroups (k : ℕ) (G : Type*) [Group G] : Prop :=
  ∃ (H : Fin k → Subgroup G),
    (∀ i, ∀ a b : G, a ∈ H i → b ∈ H i → a * b = b * a) ∧
    ∀ g : G, ∃ i, g ∈ H i

/-- h(n) is the least k such that every group (in Type, i.e. the small universe)
    satisfying the n-commuting property can be covered by at most k Abelian
    subgroups. -/
noncomputable def erdosH (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∀ (G : Type) [Group G],
    HasNCommutingProperty n G → CoveredByAbelianSubgroups k G}

/--
Erdős Problem #117 [Er90, Er97f, Va99], with Pyber's estimate [Py87] (PROVED; the problem of
estimating h(n) as well as possible stays OPEN):

Let h(n) be minimal such that any group G satisfying the property that every
subset of more than n elements contains distinct commuting elements x ≠ y
(xy = yx) can be covered by at most h(n) Abelian subgroups.

Pyber [Py87] proved there exist constants c₂ > c₁ > 1 such that
  c₁^n < h(n) < c₂^n
for all sufficiently large n. It cannot hold for all n ≥ 1, because h(1) = h(2) = 1. The
lower bound was already known to Isaacs [Er97f]. The precise exponential growth rate of h(n)
remains open.
-/
theorem erdos_problem_117 :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ ^ n < (erdosH n : ℝ) ∧ (erdosH n : ℝ) < c₂ ^ n :=
  sorry

/--
Small values (PROVED): h(1) = h(2) = 1. With n = 1 every two distinct elements commute. With
n = 2, a non-abelian group has the three pairwise non-commuting elements x, y, xy. Either way
the group is abelian, and it is covered by the single subgroup ⊤.
-/
theorem erdos_problem_117.variants.small_values :
    erdosH 1 = 1 ∧ erdosH 2 = 1 :=
  sorry

/--
The first-pass statement, which asserts the bounds for every n ≥ 1, is false (PROVED): at
n = 1 it would need c₁ < h(1) = 1 with c₁ > 1.
-/
theorem erdos_problem_117.variants.first_pass_false :
    ¬ (∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
    ∀ n : ℕ, 1 ≤ n →
      c₁ ^ n < (erdosH n : ℝ) ∧ (erdosH n : ℝ) < c₂ ^ n) :=
  sorry
