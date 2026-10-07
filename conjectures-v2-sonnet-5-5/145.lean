-- [AI - Claude Sonnet 5.5]: Erdős Problem 145 — second-pass formalization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

open Finset Filter Topology BigOperators Classical

noncomputable section

/-!
# Erdős Problem #145: Moments of the gaps between squarefree numbers

*Source:* [erdosproblems.com/145](https://www.erdosproblems.com/145) (banner **OPEN**: "This is open, and
cannot be resolved with a finite computation."; page last edited 19 October 2025; captured 2026-03-05 as the
tidied problem box). [Er65b] [Er79] [Er81h, p.176]

Let $s_1<s_2<\cdots$ be the sequence of squarefree numbers. Is it true that, for any $\alpha \geq 0$,
$$\lim_{x\to \infty}\frac{1}{x}\sum_{s_n\leq x}(s_{n+1}-s_n)^\alpha$$
exists?

Remarks recorded on the page:
* Erdős [Er51] proved this for all $0\leq \alpha \leq 2$, and Hooley [Ho73] extended this to all
  $\alpha \leq 3$.
* Greaves, Harman and Huxley showed (in Chapter 11 of [GHH97]) that this is true for $\alpha \leq 11/3$.
  Chan [Ch23c] has extended this to $\alpha \leq 3.75$.
* Granville [Gr98] proved that this follows (for all $\alpha \geq 0$) from the ABC conjecture.
* See also [208].

Tags: number theory. OEIS: A005117. 2 comments at capture (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31, no prize. Upstream has
`erdos_145`, category `research open`, stated as `answer(sorry) ↔ ∀ α ≥ 0, ∃ β, …`, and three `research solved`
variants for $\alpha\le2$, $\alpha\le3$ and $\alpha<11/3$.

**What the first pass got wrong, and what this file does.** The first pass defines
`nextSquarefree n := Nat.find (show ∃ m, m > n ∧ Squarefree m from sorry)`, a `sorry` inside a definition. The
value of `Nat.find` does not depend on the proof, but the definition (and every statement about it) is
formally tied to `sorryAx`, so no theorem that mentions `nextSquarefree` could be proved without the
axiom. v2 proves the existence (a prime above `n` is squarefree), keeps the name and the statement, and
`variants.nextSquarefree_spec` shows that the definition is the successor function on the squarefree numbers.

**Encoding.**
* The main theorem asserts "yes for every $\alpha\ge0$", the asked direction while the problem is open. The
  limit is over $N\to\infty$ in ℕ. For real $x$ the sum is constant on $[N,N+1)$, and $\frac1x$ lies between
  $\frac1{N+1}$ and $\frac1N$, so the two limits exist together and agree.
* The sum is over squarefree `s ≤ N` (`0` is not squarefree), and the gap is `nextSquarefree s - s`, the distance to
  the next squarefree number, which may lie beyond `N`, as on the page. The subtraction is in ℕ and does not
  truncate, since `s < nextSquarefree s`. The exponent `α` is real, so the power is `Real.rpow`, and the base is
  at least `1`.
* `gapMoment α N` is the average in the theorem, and `variants.main_iff` shows that the theorem says
  `∀ α ≥ 0, ∃ L, Tendsto (gapMoment α) atTop (𝓝 L)`.
* `variants.nextSquarefree_seven` and `variants.gapMoment_one_seven` check the encoding on a hand-computed
  case: `nextSquarefree 7 = 10`, since `8` and `9` are not squarefree, and `gapMoment 1 7 = 9 / 7`, from the
  gaps `1, 1, 2, 1, 1, 3` after `1, 2, 3, 5, 6, 7`.
* `variants.le_two`, `le_three`, `le_eleven_thirds` and `le_chan` are the partial results of the first
  two remarks, and `variants.abc_implies` is Granville's result, with the ABC conjecture written out as
  `ABCConjecture`. The page says $\alpha\le11/3$ for [GHH97], while upstream has $\alpha<11/3$. v2 follows the
  page. **DEFERRED:** the endpoint was not checked against the source.

## References

* [Er65b] Erdős, P., _Some recent advances and current problems in number theory_. In: Lectures on Modern
  Mathematics, Vol. III (1965), 196–244.
* [Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. (1979), 67–70.
* [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_. In: Analytic
  number theory (Philadelphia, Pa., 1980) (1981), 171–182. The page cites p. 176.
* [Er51] Erdős, P., _Some problems and results in elementary number theory_. Publ. Math. Debrecen (1951),
  103–109.
* [Ho73] Hooley, C., _On the intervals between consecutive terms of sequences_. In: Proc. Sympos. Pure Math.,
  vol. 24 (1973), 129–140.
* [GHH97] Greaves, G. R. H., Harman, G. and Huxley, M. N., _Sieve methods, exponential sums, and their
  applications in number theory_ (1997). Chapter 11.
* [Ch23c] Chan (the page's key). **DEFERRED:** no bibliographic data was recovered.
* [Gr98] Granville (the page's key). **DEFERRED:** no bibliographic data was recovered.
* [208] The page's cross-reference to Problem 208.

(Provenance: [Er65b], [Er79], [Er81h] and the title and venue of [Er51] are from the bibliographies of the
`/latex` pages of other problems. [Ho73], [GHH97] and the pages of [Er51] are from the docstrings of upstream
`145.lean`. **DEFERRED:** no `/latex/145` fetch exists in the logs, so the entries were not checked against the
page's own bibliography.)
-/

/--
There is a squarefree number above every `n`: a prime above `n` is one (PROVED in Lean). This replaces the
`sorry` that the first pass had inside the definition of `nextSquarefree`.
-/
theorem erdos_problem_145.exists_squarefree_gt (n : ℕ) : ∃ m, m > n ∧ Squarefree m := by
  obtain ⟨p, hp1, hp⟩ := Nat.exists_infinite_primes (n + 1)
  exact ⟨p, by omega, hp.prime.irreducible.squarefree⟩

/--
The smallest squarefree natural number strictly greater than `n`.
-/
def nextSquarefree (n : ℕ) : ℕ :=
  Nat.find (erdos_problem_145.exists_squarefree_gt n)

/--
Erdős Problem #145 [Er65b, Er79, Er81h] — OPEN:

Let s₁ < s₂ < ⋯ be the sequence of squarefree numbers. Is it true that for any
α ≥ 0 the limit
  lim_{N → ∞} (1/N) · ∑_{squarefree s ≤ N} (nextSquarefree(s) - s)^α
exists?

Erdős [Er51] proved this for 0 ≤ α ≤ 2; Hooley [Ho73] extended it to α ≤ 3; Greaves–Harman–Huxley [GHH97]
to α ≤ 11/3; and Chan [Ch23c] to α ≤ 3.75. Granville [Gr98] showed the full conjecture follows
from the ABC conjecture.
-/
theorem erdos_problem_145 (α : ℝ) (hα : 0 ≤ α) :
    ∃ L : ℝ, Tendsto
      (fun N : ℕ =>
        (↑N)⁻¹ *
          ((Finset.range (N + 1)).filter (fun n => Squarefree n)).sum
            (fun s => ((nextSquarefree s - s : ℕ) : ℝ) ^ α))
      atTop (nhds L) :=
  sorry

/--
`nextSquarefree` is the successor function on the squarefree numbers (PROVED in Lean): `nextSquarefree n` is
above `n`, squarefree, and below every squarefree number above `n`.
-/
theorem erdos_problem_145.variants.nextSquarefree_spec (n : ℕ) :
    n < nextSquarefree n ∧ Squarefree (nextSquarefree n) ∧
      ∀ m, n < m → Squarefree m → nextSquarefree n ≤ m := by
  refine ⟨(Nat.find_spec (erdos_problem_145.exists_squarefree_gt n)).1,
    (Nat.find_spec (erdos_problem_145.exists_squarefree_gt n)).2, ?_⟩
  intro m hm hsq
  exact Nat.find_min' (erdos_problem_145.exists_squarefree_gt n) ⟨hm, hsq⟩

/-- A criterion for the value of `nextSquarefree` (PROVED in Lean), used for the hand-computed checks. -/
theorem erdos_problem_145.variants.nextSquarefree_eq_iff {n m : ℕ} :
    nextSquarefree n = m ↔
      (m > n ∧ Squarefree m) ∧ ∀ k, k < m → ¬ (k > n ∧ Squarefree k) :=
  Nat.find_eq_iff (erdos_problem_145.exists_squarefree_gt n)

/-- `nextSquarefree 7 = 10`, because `8` and `9` are not squarefree (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_seven : nextSquarefree 7 = 10 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, hsq⟩
  interval_cases k <;> exact absurd hsq (by decide +kernel)

/-- `nextSquarefree 1 = 2` (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_one : nextSquarefree 1 = 2 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, _⟩
  omega

/-- `nextSquarefree 2 = 3` (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_two : nextSquarefree 2 = 3 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, _⟩
  omega

/-- `nextSquarefree 3 = 5`, because `4` is not squarefree (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_three : nextSquarefree 3 = 5 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, hsq⟩
  interval_cases k
  exact absurd hsq (by decide +kernel)

/-- `nextSquarefree 5 = 6` (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_five : nextSquarefree 5 = 6 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, _⟩
  omega

/-- `nextSquarefree 6 = 7` (PROVED in Lean). -/
theorem erdos_problem_145.variants.nextSquarefree_six : nextSquarefree 6 = 7 := by
  rw [erdos_problem_145.variants.nextSquarefree_eq_iff]
  refine ⟨⟨by norm_num, by decide +kernel⟩, ?_⟩
  intro k hk ⟨hkn, _⟩
  omega

/-- The average of the page: `(1/N) * ∑_{squarefree s ≤ N} (nextSquarefree s - s) ^ α`. -/
def gapMoment (α : ℝ) (N : ℕ) : ℝ :=
  (↑N)⁻¹ * ((Finset.range (N + 1)).filter (fun n => Squarefree n)).sum
    (fun s => ((nextSquarefree s - s : ℕ) : ℝ) ^ α)

/-- The main theorem says `∀ α ≥ 0, ∃ L, Tendsto (gapMoment α) atTop (𝓝 L)` (PROVED in Lean). -/
theorem erdos_problem_145.variants.main_iff :
    (∀ α : ℝ, 0 ≤ α → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L)) ↔
    ∀ α : ℝ, 0 ≤ α → ∃ L : ℝ, Tendsto
      (fun N : ℕ =>
        (↑N)⁻¹ *
          ((Finset.range (N + 1)).filter (fun n => Squarefree n)).sum
            (fun s => ((nextSquarefree s - s : ℕ) : ℝ) ^ α))
      atTop (nhds L) :=
  Iff.rfl

/--
A hand-computed check of the encoding (PROVED in Lean): the squarefree numbers up to `7` are
`1, 2, 3, 5, 6, 7`, their gaps to the next squarefree number are `1, 1, 2, 1, 1, 3` (the last one crosses
`N = 7`), so `gapMoment 1 7 = 9 / 7`.
-/
theorem erdos_problem_145.variants.gapMoment_one_seven : gapMoment 1 7 = 9 / 7 := by
  have hset : (Finset.range 8).filter (fun n => Squarefree n) = {1, 2, 3, 5, 6, 7} := by
    decide +kernel
  unfold gapMoment
  rw [show (7 : ℕ) + 1 = 8 from rfl, hset]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [erdos_problem_145.variants.nextSquarefree_one, erdos_problem_145.variants.nextSquarefree_two,
    erdos_problem_145.variants.nextSquarefree_three, erdos_problem_145.variants.nextSquarefree_five,
    erdos_problem_145.variants.nextSquarefree_six, erdos_problem_145.variants.nextSquarefree_seven]
  norm_num

/-- Erdős [Er51] (PROVED, not checked here): the limit exists for `0 ≤ α ≤ 2`. -/
theorem erdos_problem_145.variants.le_two :
    ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 2 → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L) :=
  sorry

/-- Hooley [Ho73] (PROVED, not checked here): the limit exists for `0 ≤ α ≤ 3`. -/
theorem erdos_problem_145.variants.le_three :
    ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 3 → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L) :=
  sorry

/--
Greaves, Harman and Huxley [GHH97] (PROVED, not checked here): the limit exists for `0 ≤ α ≤ 11 / 3`, as the
page words it. Upstream states `α < 11 / 3`. **DEFERRED:** the endpoint was not checked against the source.
-/
theorem erdos_problem_145.variants.le_eleven_thirds :
    ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) (11 / 3) → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L) :=
  sorry

/-- Chan [Ch23c] (PROVED, not checked here): the limit exists for `0 ≤ α ≤ 3.75`. -/
theorem erdos_problem_145.variants.le_chan :
    ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) (15 / 4) → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L) :=
  sorry

/--
The ABC conjecture: for every `ε > 0` there is `K` with `c ≤ K * rad(a b c) ^ (1 + ε)` for all coprime positive
`a`, `b` with `a + b = c`, where `rad` is the product of the primes dividing `a * b * c`.
-/
def ABCConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
    (c : ℝ) ≤ K * ((∏ p ∈ (a * b * c).primeFactors, (p : ℝ)) ^ (1 + ε))

/--
Granville [Gr98] (PROVED, not checked here): the ABC conjecture implies the full statement, for all `α ≥ 0`.
-/
theorem erdos_problem_145.variants.abc_implies (h : ABCConjecture) :
    ∀ α : ℝ, 0 ≤ α → ∃ L : ℝ, Tendsto (gapMoment α) atTop (nhds L) :=
  sorry

end
