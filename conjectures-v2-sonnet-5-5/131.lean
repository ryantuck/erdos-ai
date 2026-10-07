-- [AI - Claude Sonnet 5.5]: Erdős Problem 131 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

/-!
# Erdős Problem #131: Non-Dividing Subsets of $\{1,\ldots,N\}$

*Source:* [erdosproblems.com/131](https://www.erdosproblems.com/131) (banner **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-02-20 as the tidied
problem box). [Er75b, p.309] [Er97b, p.230] [ELRSS99, p.129]

Let $F(N)$ be the maximal size of $A\subseteq\{1,\ldots,N\}$ such that no $a\in A$ divides the sum
of any distinct elements of $A\backslash\{a\}$. Estimate $F(N)$. In particular, is it true that
$$F(N) > N^{1/2-o(1)}?$$

Remarks recorded on the page:
* This was studied by Erdős, Lev, Rauzy, Sándor, and Sárközy [ELRSS99], where they call such a
  property 'non-dividing', and prove the explicit bound $F(N)<3N^{1/2}+1$. In [Er97b] Erdős credits
  Csaba with a construction that proves $F(N) \gg N^{1/5}$. Such a construction was also given in
  [ELRSS99], where it is linked to the problem of non-averaging sets (see [186]).
* Indeed, every such set is non-averaging, and hence the result of Pham and Zakharov [PhZa24]
  implies $F(N) \leq N^{1/4+o(1)}$. This shows the answer to the original question is no, but the
  general question of the correct growth of $F(N)$ remains open.
* In [Er75b] Erdős writes that he originally thought $F(N) <(\log N)^{O(1)}$, but that Straus
  proved that $F(N) > \exp((\sqrt{\tfrac{2}{\log 2}}+o(1))\sqrt{\log N})$. See also [13].
* This is discussed in problem C16 of Guy's collection [Gu04].

Tags: number theory. OEIS: A068063. Page last edited 30 September 2025; 0 comments.

**Status.** The banner reads OPEN because the general question of the growth of $F(N)$ is open.
The explicit question "is $F(N) > N^{1/2-o(1)}$?" is answered no by the page's own remark. The
mirror (`teorth/erdosproblems`) has `open` (2025-08-31), and upstream has no `131.lean`.

**What the first pass stated, and what this file does.** The first pass stated
$F(N)\ge N^{1/4-\varepsilon}$, that the Pham–Zakharov upper bound is tight. That is neither the
page's question nor a conjecture made on the page. This file makes the page's explicit question the
main theorem, asserted as `¬ (…)` since the answer is no, which is the corpus convention for a
refuted statement. The first pass's statement is kept byte-identical as `variants.pz_tight` and
labelled OPEN and editorial.

**Encoding.**
* `IsNonDividing A` says that for every `a ∈ A` and every nonempty `S ⊆ A.erase a`, `a` does not
  divide `∑ S`. The page's "the sum of any distinct elements" is read as the sum of any nonempty
  set of distinct elements, singletons included, so a divisibility antichain is part of the
  property. The other natural reading, sums of at least two elements, gives different values at
  small $N$: exhaustive search for $N\le45$ gives $F(2)=1$ against $2$ and $F(16)=4$ against $5$.
  The two maxima satisfy $F_1\le F_2\le(\log_2N+1)F_1$, because the elements with a fixed number
  of prime factors form a divisibility antichain and subsets of a valid set stay valid. So every
  statement about exponents is independent of the reading, including the main theorem,
  `pz_upper` and `pz_tight`. Only a constant-factor statement such as `csaba_lower` can depend on
  it. The page's OEIS sequence A068063 might settle the reading, but it was not recoverable
  offline.
* `erdos131F N` is the `sSup` of a set that contains $0$ (the empty set is non-dividing) and is
  bounded by $N$, so it is the true maximum, attained.
* "$F(N) > N^{1/2-o(1)}$" is read as: for every $\varepsilon>0$, $F(N)>N^{1/2-\varepsilon}$ for all
  large $N$. That is equivalent to the existence of some $\varepsilon(N)\to0$ with
  $F(N)>N^{1/2-\varepsilon(N)}$.
* `IsNonAveraging A` says that no element is the arithmetic mean of two or more other distinct
  elements, as on the page of Problem 186 and in the first pass of that problem.

## References

* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées
  Arithmétiques de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310.
* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [ELRSS99] Erdős, P., Lev, V., Rauzy, G., Sándor, C. and Sárközy, A., _Greedy algorithm,
  arithmetic progressions, subset sums and divisibility_. Discrete Math. (1999), 119–135.
* [PhZa24] Pham, H. T. and Zakharov, D., _Sharp bound for the Erdős–Straus non-averaging set
  problem_. arXiv:2410.14624 (2024).
* [Gu04] Guy, R. K., _Unsolved Problems in Number Theory_. (2004), xviii+437. The page cites
  problem C16.

(Provenance: all five entries are from the `/latex/131` fetch in the session logs. Csaba and Straus
are credited on the page with no key of their own.)
-/

/-- A finite set A ⊆ ℕ is *non-dividing* if for every a ∈ A and every
    nonempty S ⊆ A \ {a}, the element a does not divide the sum ∑_{s ∈ S} s. -/
def IsNonDividing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → S.Nonempty → ¬(a ∣ S.sum id)

/-- F(N) is the maximal cardinality of a non-dividing subset of {1,...,N}. -/
noncomputable def erdos131F (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonDividing A ∧ A.card = k}

/-- A finite set A ⊆ ℕ is *non-averaging* if no element a ∈ A is the arithmetic mean of two or
    more distinct elements of A \ {a}: for every S ⊆ A \ {a} with |S| ≥ 2, |S| · a ≠ ∑ S. -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

/--
Erdős Problem #131 [Er75b, Er97b], the page's explicit question: "is it true that
F(N) > N^(1/2-o(1))?" — answered NO by the page's own remark (Pham–Zakharov [PhZa24], since every
non-dividing set is non-averaging). The statement asserts that answer: it is not true that for
every ε > 0 the inequality F(N) > N^(1/2-ε) holds for all large N.

The general question of the correct growth of F(N) remains open and is not a precise statement;
see `variants.pz_tight` for the first pass's guess. The statement follows from
`variants.pz_upper` by `variants.main_of_pz_upper`.
-/
theorem erdos_problem_131 :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) > (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) :=
  sorry

/--
Pham–Zakharov [PhZa24] (PROVED, as the page of Problem 186 words it): for every ε > 0 and all
large N, every non-averaging subset of {1, ..., N} has at most N^(1/4+ε) elements.
-/
theorem erdos_problem_131.variants.pz_non_averaging :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → IsNonAveraging A → (A.card : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry

/--
Every non-dividing set is non-averaging (PROVED in Lean; the page's "indeed, every such set is
non-averaging"): if |S| · a = ∑ S for a set S of at least two other elements, then a divides ∑ S.
-/
theorem erdos_problem_131.variants.non_dividing_non_averaging (A : Finset ℕ)
    (hA : IsNonDividing A) : IsNonAveraging A := by
  intro a ha S hS hcard heq
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  exact hA a ha S hS hne (Dvd.intro_left S.card heq)

/--
The Pham–Zakharov upper bound for non-dividing sets (PROVED in Lean from `pz_non_averaging` and
`non_dividing_non_averaging`): F(N) ≤ N^(1/4+ε) for every ε > 0 and all large N.
-/
theorem erdos_problem_131.variants.pz_upper :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  filter_upwards [erdos_problem_131.variants.pz_non_averaging ε hε] with N hN
  have hne : {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonDividing A ∧ A.card = k}.Nonempty :=
    ⟨0, ∅, Finset.empty_subset _, fun a ha => by simp at ha, Finset.card_empty⟩
  have hbdd : BddAbove {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonDividing A ∧ A.card = k} :=
    ⟨N, by
      rintro k ⟨A, hA, -, rfl⟩
      simpa using Finset.card_le_card hA⟩
  obtain ⟨A, hA, hnd, hcard⟩ := Nat.sSup_mem hne hbdd
  have hF : erdos131F N = A.card := hcard.symm
  rw [hF]
  exact hN A hA (erdos_problem_131.variants.non_dividing_non_averaging A hnd)

/--
The main theorem follows from the Pham–Zakharov upper bound (PROVED): with ε = 1/16 the upper bound
is N^(5/16), which is below N^(3/8) = N^(1/2-1/8) for N ≥ 2.
-/
theorem erdos_problem_131.variants.main_of_pz_upper
    (hpz : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε)) :
    ¬ (∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) > (N : ℝ) ^ ((1 : ℝ) / 2 - ε)) := by
  intro h
  obtain ⟨N, h1, h2, h3⟩ := ((h (1 / 8) (by norm_num)).and
    ((hpz (1 / 16) (by norm_num)).and (eventually_ge_atTop 2))).exists
  have hN : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hlt : (N : ℝ) ^ ((1 : ℝ) / 4 + 1 / 16) < (N : ℝ) ^ ((1 : ℝ) / 2 - 1 / 8) :=
    Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)
  linarith

/--
Erdős–Lev–Rauzy–Sándor–Sárközy [ELRSS99] (PROVED; not checked here): F(N) < 3 N^(1/2) + 1.
-/
theorem erdos_problem_131.variants.elrss_upper :
    ∀ N : ℕ, (erdos131F N : ℝ) < 3 * Real.sqrt (N : ℝ) + 1 :=
  sorry

/--
Csaba's construction (PROVED; credited in [Er97b] and given again in [ELRSS99], not checked here):
F(N) ≫ N^(1/5). The constant-factor form is stated for the reading of "distinct elements" used in
this file. For the other reading the same construction would give the bound up to a factor
log N, which is the same exponent.
-/
theorem erdos_problem_131.variants.csaba_lower :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 5) ≤ (erdos131F N : ℝ) :=
  sorry

/--
The first pass's statement (OPEN; editorial, not stated on the page): the Pham–Zakharov upper bound
is essentially tight, F(N) ≥ N^(1/4-ε) for any ε > 0 and all sufficiently large N. Together with
`pz_upper` it says F(N) = N^(1/4+o(1)). The known lower bound is N^(1/5).
-/
theorem erdos_problem_131.variants.pz_tight :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (erdos131F N : ℝ) ≥ (N : ℝ) ^ ((1 : ℝ) / 4 - ε) :=
  sorry
