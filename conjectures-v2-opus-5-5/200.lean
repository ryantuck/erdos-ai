-- [AI - Claude Opus 5.5]: Erdős Problem 200 — second-pass formalization
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat

open Filter Asymptotics Real

/-!
# Erdős Problem #200

*Source:* [erdosproblems.com/200](https://www.erdosproblems.com/200) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05). [ErGr79] [ErGr80]

Does the longest arithmetic progression of primes in $\{1,\ldots,N\}$ have length $o(\log N)$?

Remarks recorded on the page: it follows from the prime number theorem that such a progression
has length $\leq(1+o(1))\log N$. OEIS A005115.

## Encoding notes

* The theorem asserts the "yes" answer (OPEN; corpus convention for open questions).
* `longestPrimeAP N` is an `sSup` over a set that contains `0` and is bounded by `N`, since a
  `k`-term progression with `d > 0` inside `{1, …, N}` has `k` distinct terms (`longestPrimeAP_le`,
  PROVED in Lean); so it is the maximum. For example `3 ≤ longestPrimeAP 7`, from `3, 5, 7`
  (`three_le_longestPrimeAP_seven`, PROVED).
* By the Green–Tao theorem the length tends to infinity, so the question is about its rate.

## References

No `/latex/200` fetch is in the session logs; the page cites only Erdős and Graham.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/200.lean` (Opus 5.5 review, `opus-5-5-review/200.md`).
-/

/--
A set S ⊆ ℕ is an arithmetic progression of length k if there exist a, d such that
S = {a, a+d, a+2d, ..., a+(k-1)d} with d > 0.
-/
def IsArithProgressionOfLength (S : Finset ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ S = Finset.image (fun i => a + d * i) (Finset.range k)

/--
The length of the longest arithmetic progression of primes in {1, ..., N}.
-/
noncomputable def longestPrimeAP (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset ℕ, IsArithProgressionOfLength S k ∧
    (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, 1 ≤ p ∧ p ≤ N)}

/--
Erdős Problem #200 [ErGr79, ErGr80]:

Does the longest arithmetic progression of primes in {1, …, N} have length o(log N)?

It follows from the prime number theorem that such a progression has length
≤ (1 + o(1)) log N. (Status: OPEN; the "yes" direction is asserted.)
-/
theorem erdos_problem_200 :
    (fun N => (longestPrimeAP N : ℝ)) =o[atTop] (fun N => log (N : ℝ)) :=
  sorry

/-- A progression of primes of length `k` inside `{1, …, N}` has `k ≤ N` (PROVED in Lean). -/
theorem erdos_problem_200.le_of_mem {N k : ℕ}
    (h : ∃ S : Finset ℕ, IsArithProgressionOfLength S k ∧
      (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, 1 ≤ p ∧ p ≤ N)) : k ≤ N := by
  obtain ⟨S, ⟨a, d, hd, rfl⟩, -, hS⟩ := h
  have hinj : Function.Injective (fun i => a + d * i) := fun i j hij => by
    simp only at hij
    exact Nat.eq_of_mul_eq_mul_left hd (by omega)
  have hcard := Finset.card_image_of_injective (Finset.range k) hinj
  rw [Finset.card_range] at hcard
  have hsub : Finset.image (fun i => a + d * i) (Finset.range k) ⊆ Finset.Icc 1 N :=
    fun p hp => Finset.mem_Icc.2 (hS p hp)
  have hle := Finset.card_le_card hsub
  rw [hcard, Nat.card_Icc] at hle
  omega

/-- `longestPrimeAP N ≤ N`: the `sSup` is over a nonempty set bounded by `N` (PROVED in Lean). -/
theorem erdos_problem_200.longestPrimeAP_le (N : ℕ) : longestPrimeAP N ≤ N := by
  unfold longestPrimeAP
  refine csSup_le ⟨0, ∅, ⟨0, 1, one_pos, by simp⟩, by simp, by simp⟩ fun k hk => ?_
  exact erdos_problem_200.le_of_mem hk

/-- Sanity check (PROVED in Lean): `3, 5, 7` gives `3 ≤ longestPrimeAP 7`. -/
theorem erdos_problem_200.three_le_longestPrimeAP_seven : 3 ≤ longestPrimeAP 7 := by
  unfold longestPrimeAP
  exact le_csSup ⟨7, fun k hk => erdos_problem_200.le_of_mem hk⟩
    ⟨_, ⟨3, 2, two_pos, rfl⟩, by decide, by decide⟩

/-- The page's upper bound from the prime number theorem (SOLVED; not proved here): the length is at
most $(1+o(1))\log N$. -/
theorem erdos_problem_200.variants.pnt_upper :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (longestPrimeAP N : ℝ) ≤ (1 + ε) * log (N : ℝ) :=
  sorry

/-- The Green–Tao theorem (SOLVED; not proved here): the length tends to infinity. -/
theorem erdos_problem_200.variants.green_tao :
    Tendsto longestPrimeAP atTop atTop :=
  sorry
