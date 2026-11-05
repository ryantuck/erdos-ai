-- [AI - Claude Opus 5.5]: Erdős Problem 186 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Real.Sqrt

open Filter

noncomputable section

/-!
# Erdős Problem #186

*Source:* [erdosproblems.com/186](https://www.erdosproblems.com/186) (status **SOLVED**: "This has
been resolved in some other way than a proof or disproof."; captured 2026-02-20; page edited
06 October 2025). [Er73, p.118] [Er75b, p.309] [Er77c, p.45] [ErGr79, p.334] [ErGr80, p.18]

Let $F(N)$ be the maximal size of $A\subseteq \{1,\ldots,N\}$ which is 'non-averaging', so that no
$n\in A$ is the arithmetic mean of at least two elements in $A$. What is the order of growth of
$F(N)$?

Remarks recorded on the page (abridged): originally due to Straus. It is known that
$N^{1/4}\ll F(N) \ll N^{1/4+o(1)}$. The lower bound is due to Bosznay [Bo89] and the upper bound to
Pham and Zakharov [PhZa24], improving an earlier bound of Conlon, Fox, and Pham [CFP23]. The
original upper bound of Erdős and Sárközy [ErSa90] was $\ll (N\log N)^{1/2}$. See also [789]. This
is discussed in problem C16 of Guy's collection [Gu04]. OEIS A389784.

## Encoding notes

* `IsNonAveraging` takes the averaged sets inside `A \ {a}`. Allowing `a` itself in the set changes
  nothing: removing `a` from a set with mean `a` leaves a set with mean `a`, and one remaining
  element would have to equal `a`.
* The main theorem, $N^{1/4-\varepsilon}\le F(N)\le N^{1/4+\varepsilon}$ eventually, is
  $F(N)=N^{1/4+o(1)}$. It follows from the two recorded bounds (`variants.main_of_bounds`, PROVED
  in Lean); Bosznay's lower bound $F(N)\gg N^{1/4}$ is stronger than its lower half.
* `nonAvgMax N` is a maximum over a nonempty set bounded by `N` (`nonAvgMax_le`, PROVED). Sanity
  checks by `decide`: $\{1,2,3\}$ is not non-averaging, $\{1,2,4\}$ is.

## References

From the site's `/latex/186` bibliography:
* [Bo89] Bosznay, Á. P., _On the lower estimation of nonaveraging sets_. Acta Math. Hungar. (1989),
  155–157.
* [CFP23] Conlon, D., Fox, J. and Pham, H. T., _Homogeneous structures in subset sums and
  non-averaging sets_. arXiv:2311.01416 (2023).
* [ErSa90] Erdős, P. and Sárközy, A., _On a problem of Straus_. Disorder in Physical Systems (1990),
  55–66.
* [Gu04] Guy, Richard K., _Unsolved Problems in Number Theory_ (2004), xviii+437.
* [PhZa24] Pham, H. T. and Zakharov, D., _Sharp bound for the Erdős–Straus non-averaging set
  problem_. arXiv:2410.14624 (2024).

Erdős's sources:
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of
  combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971)
  (1973), 117–138. (Site `/latex/783` and others.)
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques
  de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310. (Site `/latex/656` and
  others.)
* [Er77c] Erdős, Paul, _Problems and results on combinatorial number theory. III_. Number theory
  day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72. (Site `/latex/460` and
  others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/186.lean` (Opus 5.5 review, `opus-5-5-review/186.md`).
-/

/-- A finite set A of natural numbers is *non-averaging* if no element a ∈ A is
    the arithmetic mean of two or more distinct elements in A \ {a}. Equivalently,
    for every a ∈ A and every S ⊆ A \ {a} with |S| ≥ 2, we have |S| · a ≠ ∑ S. -/
def IsNonAveraging (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ A.erase a → 2 ≤ S.card → S.card * a ≠ S.sum id

/-- F(N) is the maximal cardinality of a non-averaging subset of {1,…,N}. -/
noncomputable def nonAvgMax (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsNonAveraging A ∧ A.card = k}

/--
Erdős Problem #186 [Er73, Er75b, Er77c, ErGr79, ErGr80]:

The maximal size F(N) of a non-averaging subset of {1,…,N} satisfies
F(N) = N^{1/4+o(1)}, i.e., for every ε > 0,

  N^{1/4-ε} ≤ F(N) ≤ N^{1/4+ε}

for all sufficiently large N.

The lower bound N^{1/4} ≪ F(N) is due to Bosznay [Bo89], and the upper bound
F(N) ≪ N^{1/4+o(1)} is due to Pham and Zakharov [PhZa24]. (Status: SOLVED.)
-/
theorem erdos_problem_186 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (nonAvgMax N : ℝ) ∧
        (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry

/-- `IsNonAveraging A` is decidable (the quantifier over `S` ranges over subsets of a finite set). -/
instance (A : Finset ℕ) : Decidable (IsNonAveraging A) := by
  unfold IsNonAveraging
  infer_instance

/-- Sanity check (PROVED by `decide`): $\{1,2,3\}$ is not non-averaging, since $2=(1+3)/2$. -/
theorem erdos_problem_186.not_isNonAveraging_one_two_three : ¬ IsNonAveraging {1, 2, 3} := by
  decide

/-- Sanity check (PROVED by `decide`): $\{1,2,4\}$ is non-averaging. -/
theorem erdos_problem_186.isNonAveraging_one_two_four : IsNonAveraging {1, 2, 4} := by
  decide

/-- Sanity check (PROVED by `decide`): averages of three or more elements count. $\{1,5,6,8\}$ has
no element that is the mean of two others, but $5=(1+6+8)/3$. -/
theorem erdos_problem_186.not_isNonAveraging_one_five_six_eight :
    ¬ IsNonAveraging {1, 5, 6, 8} := by
  decide

/-- The trivial bound $F(N)\le N$; in particular the `sSup` is over a nonempty set bounded above
(PROVED in Lean). -/
theorem erdos_problem_186.nonAvgMax_le (N : ℕ) : nonAvgMax N ≤ N := by
  unfold nonAvgMax
  refine csSup_le ⟨0, ∅, Finset.empty_subset _, fun a ha => by simp at ha, rfl⟩ ?_
  rintro k ⟨A, hA, -, rfl⟩
  simpa using Finset.card_le_card hA

/-- Bosznay's lower bound $F(N)\gg N^{1/4}$ [Bo89] (SOLVED; not proved here). -/
theorem erdos_problem_186.variants.bosznay :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (nonAvgMax N : ℝ) :=
  sorry

/-- Pham and Zakharov's upper bound $F(N)\le N^{1/4+o(1)}$ [PhZa24] (SOLVED; not proved here). -/
theorem erdos_problem_186.variants.pham_zakharov :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) :=
  sorry

/-- The original upper bound of Erdős and Sárközy [ErSa90], $F(N)\ll(N\log N)^{1/2}$ (SOLVED; not
proved here). -/
theorem erdos_problem_186.variants.erdos_sarkozy :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (nonAvgMax N : ℝ) ≤ C * Real.sqrt ((N : ℝ) * Real.log N) :=
  sorry

/-- The two recorded bounds give the main theorem (PROVED in Lean). -/
theorem erdos_problem_186.variants.main_of_bounds
    (hlo : ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (nonAvgMax N : ℝ))
    (hup : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (N : ℝ) ^ ((1 : ℝ) / 4 - ε) ≤ (nonAvgMax N : ℝ) ∧
        (nonAvgMax N : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4 + ε) := by
  intro ε hε
  obtain ⟨c, hc, hlo⟩ := hlo
  have hgrow : ∀ᶠ N : ℕ in atTop, 1 / c ≤ (N : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1 / c)
  filter_upwards [hlo, hup ε hε, hgrow, eventually_ge_atTop 1] with N h1 h2 h3 h4
  refine ⟨?_, h2⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast h4
  have hsplit : (N : ℝ) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ ((1 : ℝ) / 4 - ε) * (N : ℝ) ^ ε := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hpos : 0 < (N : ℝ) ^ ((1 : ℝ) / 4 - ε) := Real.rpow_pos_of_pos hN _
  have h5 : 1 ≤ c * (N : ℝ) ^ ε := by
    have h6 := mul_le_mul_of_nonneg_left h3 hc.le
    rwa [mul_one_div_cancel hc.ne'] at h6
  calc (N : ℝ) ^ ((1 : ℝ) / 4 - ε) = (N : ℝ) ^ ((1 : ℝ) / 4 - ε) * 1 := (mul_one _).symm
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 4 - ε) * (c * (N : ℝ) ^ ε) :=
        mul_le_mul_of_nonneg_left h5 hpos.le
    _ = c * (N : ℝ) ^ ((1 : ℝ) / 4) := by rw [hsplit]; ring
    _ ≤ (nonAvgMax N : ℝ) := h1

end
