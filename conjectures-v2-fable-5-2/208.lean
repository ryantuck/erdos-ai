-- [AI - Claude Fable 5.2]: Erdős Problem 208 — second-pass formalization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.Basic

open Filter Topology Real Classical

/-!
# Erdős Problem #208

*Source:* [erdosproblems.com/208](https://www.erdosproblems.com/208) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; captured 2026-03-05; page last edited
19 October 2025). [Er51] [Er61] [Er65b] [Er79] [Er81h, p.176]

Let $s_1<s_2<\cdots$ be the sequence of squarefree numbers. Is it true that, for any $\epsilon>0$
and large $n$,
$$s_{n+1}-s_n \ll_\epsilon s_n^{\epsilon}?$$
Is it true that
$$s_{n+1}-s_n \leq (1+o(1))\frac{\pi^2}{6}\frac{\log s_n}{\log\log s_n}?$$

Remarks recorded on the page: Erdős [Er51] showed that there are infinitely many $n$ such that
$$s_{n+1}-s_n > (1+o(1))\frac{\pi^2}{6}\frac{\log s_n}{\log\log s_n},$$
so this bound would be the best possible. In [Er79] Erdős says perhaps $s_{n+1}-s_n \ll \log s_n$,
but he is 'very doubtful'. Filaseta and Trifonov [FiTr92] proved an upper bound of
$s_n^{1/5+o(1)}$. Pandey [Pa24] has improved this exponent to $1/5-c$ for some constant $c>0$.
Granville [Gr98] showed that $s_{n+1}-s_n\ll_\epsilon s_n^\epsilon$ for all $\epsilon>0$ follows
from the ABC conjecture. See also [489] and [145]. A more general form of this problem is given in
[1101]. OEIS A005117, A076259.

## Status

OPEN at capture and in the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12). Upstream
`formal-conjectures` (`5258ab9`) states both parts with `Nat.nth Squarefree`.

## Changes from the input

* **Defect fixed.** The input declares `def squarefreeSeq : ℕ → ℕ := sorry` and three `axiom`s
  about it. Here `squarefreeSeq` is `Nat.nth Squarefree`, and the three properties are theorems
  with the input's names and statements (`squarefreeSeq_strictMono`, `squarefreeSeq_squarefree`,
  `squarefreeSeq_surj`, PROVED in Lean). The two theorem statements are unchanged.

## Encoding notes

* Both theorems assert "yes" (OPEN; corpus convention for open yes/no questions). Erdős was 'very
  doubtful' of the weaker-looking `≪ log s_n`, which the second part implies
  (`variants.log_bound_of_part_two`, PROVED in Lean); the second part should be read with that in
  mind.
* The sequence is indexed from `0`, so `squarefreeSeq n` is the page's `s_{n+1}`; both statements
  are about all large `n`, and the shift does not matter. `squarefreeSeq 0 = 1`
  (`squarefreeSeq_zero`, PROVED in Lean).
* `(1 + o(1))` is read as: for every `δ > 0`, eventually `≤ (1 + δ) · …`.
* The second part implies the first (not proved in Lean).

## References

No `/latex/208` fetch is in the session logs; the entries below come from other problems' site
bibliographies.
* [Er51] Erdős, P., _Some problems and results in elementary number theory_. Publ. Math. Debrecen
  (1951), 103–109. (Site `/latex/222`.)
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254. (Site `/latex/511` and others.)
* [Er65b] Erdős, P., _Some recent advances and current problems in number theory_. Lectures on
  Modern Mathematics, Vol. III (1965), 196–244. (Site `/latex/976` and others.)
* [Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. (1979), 67–70.
  (Site `/latex/676` and others.)
* [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_.
  Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182. (Site `/latex/1103` and
  others.) The page cites p. 176.
* [FiTr92] Filaseta and Trifonov; [Pa24] Pandey; [Gr98] Granville. **DEFERRED:** cited in the
  page's remarks; no bibliographic data was recovered.

*Provenance:* second pass of `conjectures/208.lean` (Fable 5.2 review,
`fable-5-2-review/208.md`).
-/

noncomputable section

/--
The sequence of squarefree numbers in increasing order, indexed starting at 0.

(Second pass: the input's body was `sorry`; it is now Mathlib's `Nat.nth Squarefree`.)
-/
def squarefreeSeq : ℕ → ℕ := Nat.nth Squarefree

/-- There are infinitely many squarefree numbers: every prime is squarefree (PROVED in Lean). -/
theorem squarefreeSeq_infinite : (setOf (Squarefree : ℕ → Prop)).Infinite :=
  Nat.infinite_setOf_prime.mono fun _ hp => Irreducible.squarefree hp

/--
`squarefreeSeq` enumerates exactly the squarefree numbers in increasing order.

(Second pass: an `axiom` in the input; PROVED in Lean here.)
-/
theorem squarefreeSeq_strictMono : StrictMono squarefreeSeq :=
  Nat.nth_strictMono squarefreeSeq_infinite

/-- Every term of `squarefreeSeq` is squarefree. (Second pass: an `axiom` in the input; PROVED in
Lean here.) -/
theorem squarefreeSeq_squarefree (n : ℕ) : Squarefree (squarefreeSeq n) :=
  Nat.nth_mem_of_infinite squarefreeSeq_infinite n

/-- Every squarefree number is a term of `squarefreeSeq`. (Second pass: an `axiom` in the input;
PROVED in Lean here.) -/
theorem squarefreeSeq_surj (m : ℕ) (hm : Squarefree m) : ∃ n, squarefreeSeq n = m :=
  ⟨Nat.count Squarefree m, Nat.nth_count hm⟩

/-- The first squarefree number is `1` (PROVED in Lean); `0` is not squarefree. -/
theorem squarefreeSeq_zero : squarefreeSeq 0 = 1 := by
  have h := Nat.nth_count (p := Squarefree) (n := 1) squarefree_one
  have hc : Nat.count Squarefree 1 = 0 := by
    simp [Nat.count_succ]
  rw [hc] at h
  exact h

/-- `n + 1 ≤ squarefreeSeq n` (PROVED in Lean): the sequence is strictly increasing from `1`. -/
theorem squarefreeSeq_ge (n : ℕ) : n + 1 ≤ squarefreeSeq n := by
  induction n with
  | zero => rw [squarefreeSeq_zero]
  | succ k ih =>
    have := squarefreeSeq_strictMono (show k < k + 1 by omega)
    omega

/--
Erdős Problem #208, Part 1 [Er51, Er61, Er65b, Er79, Er81h]:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that for
any ε > 0 and all sufficiently large n,
  s_{n+1} - s_n ≪_ε s_n^ε ?

That is, for every ε > 0 there exist constants C > 0 and N₀ such that for all
n ≥ N₀, s_{n+1} - s_n ≤ C · s_n^ε.

Status: OPEN; the "yes" direction is asserted. Granville [Gr98]: it follows from the ABC
conjecture.
-/
theorem erdos_problem_208a (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        C * (squarefreeSeq n : ℝ) ^ ε :=
  sorry

/--
Erdős Problem #208, Part 2 [Er51, Er61, Er65b, Er79, Er81h]:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that
  s_{n+1} - s_n ≤ (1 + o(1)) · (π²/6) · (log s_n / log log s_n) ?

Erdős showed this bound would be best possible, as there are infinitely many n
achieving the reverse inequality.

Status: OPEN; the "yes" direction is asserted.
-/
theorem erdos_problem_208b :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        (1 + δ) * (π ^ 2 / 6) *
          (Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))) :=
  sorry

/-- Erdős [Er51] (SOLVED; not proved here): the bound of Part 2 would be best possible. For every
`δ > 0` there are infinitely many `n` with
`s_{n+1} - s_n > (1 - δ) (π²/6) log s_n / log log s_n`. -/
theorem erdos_problem_208.variants.erdos_lower :
    ∀ δ : ℝ, 0 < δ → ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      (1 - δ) * (π ^ 2 / 6) *
          (Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))) <
        (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) :=
  sorry

/-- Filaseta and Trifonov [FiTr92] (SOLVED; not proved here): `s_{n+1} - s_n ≤ s_n^(1/5 + o(1))`,
that is, Part 1 for every `ε > 1/5`. -/
theorem erdos_problem_208.variants.filaseta_trifonov (ε : ℝ) (hε : 1 / 5 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        C * (squarefreeSeq n : ℝ) ^ ε :=
  sorry

/-- Part 2 implies `s_{n+1} - s_n ≪ log s_n` (PROVED in Lean, from Part 2 as a hypothesis), the
bound of which Erdős was 'very doubtful' in [Er79]: once `log log s_n ≥ 1`, the right-hand side of
Part 2 with `δ = 1` is at most `(π²/3) log s_n`. -/
theorem erdos_problem_208.variants.log_bound_of_part_two
    (h : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤
        (1 + δ) * (π ^ 2 / 6) *
          (Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n)))) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ) ≤ C * Real.log (squarefreeSeq n) := by
  obtain ⟨N₀, hN₀⟩ := h 1 one_pos
  refine ⟨π ^ 2 / 3, by positivity, max N₀ 27, fun n hn => ?_⟩
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn27 : 27 ≤ n := le_trans (le_max_right _ _) hn
  have hs : (27 : ℝ) ≤ (squarefreeSeq n : ℝ) := by
    have := squarefreeSeq_ge n
    exact_mod_cast (by omega : 27 ≤ squarefreeSeq n)
  -- `log s ≥ log 27 = 3 log 3 > 3 > e`, so `log log s ≥ 1`
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog27 : (3 : ℝ) < Real.log 27 := by
    have h27 : (27 : ℝ) = 3 ^ (3 : ℕ) := by norm_num
    rw [h27, Real.log_pow]
    push_cast
    linarith
  have hlogs : (3 : ℝ) < Real.log (squarefreeSeq n) :=
    lt_of_lt_of_le hlog27 (Real.log_le_log (by norm_num) hs)
  have hloglog : (1 : ℝ) ≤ Real.log (Real.log (squarefreeSeq n)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans Real.exp_one_lt_d9.le (by linarith)
  have hdiv : Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n)) ≤
      Real.log (squarefreeSeq n) :=
    div_le_self (by linarith) hloglog
  have h1 := hN₀ n hn0
  have hpi : (0 : ℝ) ≤ (1 + 1) * (π ^ 2 / 6) := by positivity
  have h2 := mul_le_mul_of_nonneg_left hdiv hpi
  calc (squarefreeSeq (n + 1) - squarefreeSeq n : ℝ)
      ≤ (1 + 1) * (π ^ 2 / 6) *
          (Real.log (squarefreeSeq n) / Real.log (Real.log (squarefreeSeq n))) := h1
    _ ≤ (1 + 1) * (π ^ 2 / 6) * Real.log (squarefreeSeq n) := h2
    _ = π ^ 2 / 3 * Real.log (squarefreeSeq n) := by ring

end
