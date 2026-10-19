-- [AI - Claude Opus 5.5]: Erdős Problem 178 — second-pass formalization
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Abs

import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #178

*Source:* [erdosproblems.com/178](https://www.erdosproblems.com/178) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20). [ErGr79] [ErGr80]

Let $A_1,A_2,\ldots$ be an infinite collection of infinite sets of integers, say
$A_i=\{a_{i1}<a_{i2}<\cdots\}$. Does there exist some $f:\mathbb{N}\to\{-1,1\}$ such that
$\max_{m, 1\leq i\leq d} \left\lvert \sum_{1\leq j\leq m} f(a_{ij})\right\rvert \ll_d 1$ for all
$d\geq 1$?

Remarks recorded on the page: Erdős remarks 'it seems certain that the answer is affirmative'. This
was solved by Beck [Be81]. Recently Beck [Be17] proved that one can replace $\ll_d 1$ with
$\ll d^{4+\epsilon}$ for any $\epsilon>0$.

After the capture, the mirror (`b916d95`) records `proved (Lean)` (2026-04-21), and upstream
`formal-conjectures` (`df3f12d`) links a Lean proof of its version of the statement. Neither proof
was examined here.

## Encoding notes

* The question is a yes/no question whose answer is yes; the statement is asserted directly.
* Each `A_i` is given by its increasing enumeration `a i : ℕ → ℕ` (`StrictMono`), indexed from `0`;
  "`1 ≤ i ≤ d`" is `i < d`, and the partial sums over `j ≤ m` are sums over `range m`. One `f` must
  work for every `d`, with a bound `C` depending on `d` (and the family).
* For a single sequence the bound `1` is attained by alternating signs along it
  (`variants.one_set`, PROVED in Lean); the difficulty is in balancing many sequences at once.

## References

From the site's `/latex/178` bibliography:
* [Be81] Beck, J., _Balancing families of integer sequences_. Combinatorica (1981), 209–216.
* [Be17] Beck, J., _A discrepancy problem: balancing infinite dimensional vectors_. Number
  theory–Diophantine problems, uniform distribution and applications (2017), 61–82.

Erdős's sources:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring; no site entry was recovered.)

*Provenance:* second pass of `conjectures/178.lean` (Opus 5.5 review, `opus-5-5-review/178.md`).
-/

/--
Erdős Problem #178 [ErGr79, ErGr80]:
Given any infinite sequence of infinite subsets of ℕ (each represented by
its strictly increasing enumeration a(i, ·) : ℕ → ℕ), there exists a
coloring f : ℕ → ℤ with f(n) ∈ {-1, 1} such that for each d, the partial
sums of f along the first d sequences are uniformly bounded by a constant
depending only on d.

Proved by Beck [Be81]. (Status: PROVED; the statement is the true direction.)
-/
theorem erdos_problem_178 :
    ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) →
      ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
        ∀ d : ℕ, ∃ C : ℤ, 0 < C ∧
          ∀ m i, i < d → abs (∑ j ∈ Finset.range m, f (a i j)) ≤ C :=
  sorry

/-- Partial sums of `(-1)^i` are `k % 2` (PROVED in Lean). -/
theorem erdos_problem_178.sum_neg_one_pow (k : ℕ) : ∑ i ∈ Finset.range k, (-1 : ℤ) ^ i = (k % 2 : ℕ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with h | h
    · rw [h.neg_one_pow, Nat.even_iff.mp h, Nat.succ_mod_two_eq_one_iff.mpr (Nat.even_iff.mp h)]
      norm_num
    · rw [h.neg_one_pow, Nat.odd_iff.mp h, Nat.succ_mod_two_eq_zero_iff.mpr (Nat.odd_iff.mp h)]
      norm_num

/-- One sequence can be balanced with bound `1`: alternate the signs along it (PROVED in Lean). -/
theorem erdos_problem_178.variants.one_set (a : ℕ → ℕ) (ha : StrictMono a) :
    ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧
      ∀ m, abs (∑ j ∈ Finset.range m, f (a j)) ≤ 1 := by
  classical
  let f : ℕ → ℤ := fun n => if h : ∃ j, a j = n then (-1) ^ (Nat.find h) else 1
  have hfa : ∀ j, f (a j) = (-1) ^ j := by
    intro j
    have h : ∃ j', a j' = a j := ⟨j, rfl⟩
    simp only [f, dif_pos h]
    congr 1
    exact ha.injective (Nat.find_spec h)
  refine ⟨f, fun n => ?_, fun m => ?_⟩
  · simp only [f]
    split_ifs
    · rcases neg_one_pow_eq_or ℤ (Nat.find ‹∃ j, a j = n›) with h | h <;> simp [h]
    · simp
  · rw [Finset.sum_congr rfl (fun j _ => hfa j), erdos_problem_178.sum_neg_one_pow]
    have : (m % 2 : ℕ) ≤ 1 := by omega
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast this

/-- Beck [Be17] (SOLVED; not proved here): the bound can be taken `≪ d ^ (4 + ε)`. Stated with a
constant `C` that may depend on the family and on `ε`. -/
theorem erdos_problem_178.variants.beck17 :
    ∀ a : ℕ → ℕ → ℕ, (∀ i, StrictMono (a i)) → ∀ ε : ℝ, 0 < ε →
      ∃ f : ℕ → ℤ, (∀ n, f n = 1 ∨ f n = -1) ∧ ∃ C : ℝ, ∀ d : ℕ, 1 ≤ d →
        ∀ m i, i < d → ((abs (∑ j ∈ Finset.range m, f (a i j)) : ℤ) : ℝ) ≤
          C * (d : ℝ) ^ ((4 : ℝ) + ε) :=
  sorry
