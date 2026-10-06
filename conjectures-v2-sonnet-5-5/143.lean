-- [AI - Claude Sonnet 5.5]: Erdős Problem 143 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.LiminfLimsup
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Real Filter Topology

noncomputable section

/-!
# Erdős Problem #143: Sets with $|kx - y| \ge 1$ are sparse

*Source:* [erdosproblems.com/143](https://www.erdosproblems.com/143) (banner **OPEN**, prize **\$500**:
"This is open, and cannot be resolved with a finite computation."; two captures on 2026-03-05, the page and
its tidied problem box, with identical content; the captures carry no last-edited date).
[Er61] [Er73] [Er77c] [Er92c] [Er97c]

Let $A\subset (1,\infty)$ be a countably infinite set such that $\lvert kx -y\rvert \geq 1$ for all
$x\neq y\in A$ and integers $k\geq 1$. Does this imply that $A$ is sparse? In particular, does
this imply that $\sum_{x\in A}\frac{1}{x\log x}<\infty$ or $\sum_{x <n,\, x\in A}\frac{1}{x}=o(\log n)$?

Remarks recorded on the page:
* If $A$ is a set of integers then the condition implies that $A$ is a primitive set (no element of $A$ is
  divisible by any other). For primitive sets the convergence of $\sum_{n\in A}\frac{1}{n\log n}$ was proved
  by Erdős [Er35], and the upper bound $\sum_{n<x,\,n\in A}\frac1n\ll\frac{\log x}{\sqrt{\log\log x}}$ by
  Behrend [Be35]. This $O(\cdot)$ bound was improved to $o(\cdot)$ by Erdős, Sárközy and Szemerédi [ESS67].
* In [Er73] and [Er77c] Erdős mentions an unpublished proof of Haight that
  $\lim\frac{\lvert A\cap[1,x]\rvert}{x}=0$ holds if the elements of $A$ are independent over $\mathbb Q$.
* Over the years Erdős asked for various quantitative estimates, for example
  $\liminf\frac{\lvert A\cap[1,x]\rvert}{x}=0$, or even (motivated by Behrend's bound)
  $\sum_{x<n,\,x\in A}\frac1x\ll\frac{\log x}{\sqrt{\log\log x}}$.
* In [Er97c] Erdős offers \$500 for resolving the questions in the main problem statement above.
* This was partially resolved by Koukoulopoulos, Lamzouri and Lichtman [KLL25], who proved that
  $\sum_{x<n,\,x\in A}\frac1x=o(\log n)$. See also [858].

Tags: primitive sets. 0 comments at capture.

**Status.** OPEN as a whole. The first sum (`erdos_problem_143a`) is OPEN. The second form
(`erdos_problem_143b`) is PROVED by [KLL25], and the page says so. The mirror (`teorth/erdosproblems`) has
`open` since 2025-08-31 with prize \$500. Upstream has `erdos_143.parts.i` (the $\liminf$ question) and
`erdos_143.parts.ii` (the first sum), both `research open`, and a TODO for the two other estimates.

**Encoding.**
* A countably infinite set $A\subset(1,\infty)$ is the range of an injective sequence `a : ℕ → ℝ` with
  `1 < a i`. The terms of both sums are positive, so summability does not depend on the enumeration.
  `ErdosSeparated a` is the separation condition for distinct indices.
* The theorem `erdos_problem_143a` asserts "yes" for the first sum, and `erdos_problem_143b` asserts "yes"
  for the second, the asked direction while a question is open (143b is proved on the page). The page's "or" is
  two alternative formulations of sparseness, so there is one theorem for each.
* The separation condition with `k = 1` gives `|a i - a j| ≥ 1`, so it already forces injectivity
  (`variants.separated_injective`). The hypothesis `ha_inj` is redundant, and kept as in the first pass.
* In `erdos_problem_143b` the sum `∑' i, if a i < n then 1 / a i else 0` is a finite sum, because
  `{i | a i < n}` is finite (`variants.finite_below`). So the `tsum` is the sum over `x ∈ A`, `x < n`, and
  there is no junk value. The strict inequality `x < n` is the page's.
* The hypotheses are satisfiable: the primes satisfy them (`variants.primes_separated`).
* `variants.b_of_a` proves that the first question implies the second, so 143b is the weaker form.
* `variants.integers_primitive`, `variants.primitive_convergence` and `variants.integers_case_of_Er35` are the
  page's first remark: for integer sets the condition makes $A$ primitive, and [Er35] then gives the first sum.
* `variants.liminf_density` is the $\liminf$ question. It follows from [KLL25] by partial summation, and
  `variants.behrend_shape` is the "even" estimate, for real sets OPEN.
* Not formalized: Haight's unpublished result (the page does not say whether the separation hypothesis is
  assumed), and Behrend's and Erdős–Sárkőzy–Szemerédi's estimates for primitive sets of integers.

## References

* [Er35] Erdős, P., _Note on sequences of integers no one of which is divisible by any other_. J. London
  Math. Soc. (1935), 126–128.
* [Be35] Behrend, F., _On sequences of numbers not divisible by another_. J. London Math. Soc. (1935), 42–45.
* [ESS67] Erdős, P., Sárközy, A. and Szemerédi, E., _On a theorem of Behrend_. **DEFERRED:** the venue and
  pages were not recovered.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221–254.
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. In: A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117–138.
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. In: Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Er92c] cited on the page. **DEFERRED:** no bibliographic data was recovered (the `/latex` page of another
  problem that was fetched for it does not contain it).
* [KLL25] Koukoulopoulos, Lamzouri and Lichtman (surnames as on the page). **DEFERRED:** the title and the
  venue were not recovered.
* [858] The page's cross-reference to Problem 858.

(Provenance: [Er35], [Be35], [Er61], [Er73], [Er77c], [Er97c] and the authors and title of [ESS67] are from
the bibliographies of the `/latex` pages of other problems. **DEFERRED:** no `/latex/143` fetch exists in the
logs, so the entries were not checked against the page's own bibliography.)
-/

/-- The Erdős separation condition: for all distinct elements x, y and all
    positive integers k, |k * x - y| ≥ 1. -/
def ErdosSeparated (a : ℕ → ℝ) : Prop :=
  ∀ i j, i ≠ j → ∀ k : ℕ, 0 < k → |↑k * a i - a j| ≥ 1

/--
Erdős Problem #143a [Er61, Er73, Er77c, Er92c, Er97c] — OPEN (\$500 offered in [Er97c] for the questions
of the main statement):
Let A ⊂ (1,∞) be a countably infinite set such that for all distinct x, y ∈ A
and positive integers k, |kx − y| ≥ 1. Does this imply that
  ∑_{x ∈ A} 1/(x log x) < ∞?
-/
theorem erdos_problem_143a
    (a : ℕ → ℝ) (ha_inj : Function.Injective a)
    (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    Summable (fun i => 1 / (a i * Real.log (a i))) :=
  sorry

/--
Erdős Problem #143b [Er61, Er73, Er77c, Er92c, Er97c] — PROVED:
Let A ⊂ (1,∞) be a countably infinite set such that for all distinct x, y ∈ A
and positive integers k, |kx − y| ≥ 1. Does this imply that
  ∑_{x < n, x ∈ A} 1/x = o(log n)?

Proved by Koukoulopoulos, Lamzouri, and Lichtman [KLL25] (not checked here).
-/
theorem erdos_problem_143b
    (a : ℕ → ℝ) (ha_inj : Function.Injective a)
    (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    Tendsto
      (fun n : ℕ =>
        (∑' i, if a i < (n : ℝ) then 1 / a i else 0) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
  sorry

/-- Separation already forces injectivity (PROVED in Lean): with `k = 1` it says `|a i - a j| ≥ 1` for
`i ≠ j`. So the hypothesis `ha_inj` of the two theorems is redundant. -/
theorem erdos_problem_143.variants.separated_injective {a : ℕ → ℝ} (h : ErdosSeparated a) :
    Function.Injective a := by
  intro i j hij
  by_contra hne
  have h1 := h i j hne 1 Nat.one_pos
  rw [hij] at h1
  norm_num at h1

/--
For a separated sequence, only finitely many terms lie below any bound (PROVED in Lean). Hence the `tsum` in
`erdos_problem_143b` is a finite sum, and not a junk value: distinct terms differ by at least `1`, so their
integer parts are distinct.
-/
theorem erdos_problem_143.variants.finite_below {a : ℕ → ℝ} (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) (x : ℝ) : {i | a i < x}.Finite := by
  refine Set.Finite.of_injOn (f := fun i => ⌊a i⌋₊)
    (t := ((Finset.range (⌈x⌉₊ + 1) : Finset ℕ) : Set ℕ)) ?_ ?_ (Finset.finite_toSet _)
  · intro i hi
    simp only [Set.mem_setOf_eq] at hi
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 : (⌊a i⌋₊ : ℝ) ≤ a i := Nat.floor_le (by linarith [ha_gt i])
    have h2 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have h3 : (⌊a i⌋₊ : ℝ) < (⌈x⌉₊ : ℝ) + 1 := by linarith
    exact_mod_cast h3
  · intro i _ j _ hij
    by_contra hne
    have hi0 : 0 ≤ a i := by linarith [ha_gt i]
    have hj0 : 0 ≤ a j := by linarith [ha_gt j]
    have h1 : (⌊a i⌋₊ : ℝ) ≤ a i := Nat.floor_le hi0
    have h2 : a i < (⌊a i⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (a i)
    have h3 : (⌊a j⌋₊ : ℝ) ≤ a j := Nat.floor_le hj0
    have h4 : a j < (⌊a j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (a j)
    have heq : (⌊a i⌋₊ : ℝ) = (⌊a j⌋₊ : ℝ) := by exact_mod_cast hij
    have hsep : (1 : ℝ) ≤ |a i - a j| := by
      have := ha_sep i j hne 1 Nat.one_pos
      simpa using this
    have hlt : |a i - a j| < 1 := by
      rw [abs_lt]
      constructor <;> linarith
    linarith

/-- The hypotheses are satisfiable (PROVED in Lean): the primes, in increasing order, are separated, because
`k * p - q` is a non-zero integer for distinct primes `p`, `q`. -/
theorem erdos_problem_143.variants.primes_separated :
    ErdosSeparated (fun i => (Nat.nth Nat.Prime i : ℝ)) := by
  intro i j hij k hk
  have hinj : Function.Injective (Nat.nth Nat.Prime) := Nat.nth_injective Nat.infinite_setOf_prime
  have hp : (Nat.nth Nat.Prime i).Prime := Nat.prime_nth_prime i
  have hq : (Nat.nth Nat.Prime j).Prime := Nat.prime_nth_prime j
  have hne : Nat.nth Nat.Prime i ≠ Nat.nth Nat.Prime j := fun h => hij (hinj h)
  have hz : ((k : ℤ) * (Nat.nth Nat.Prime i : ℤ) - (Nat.nth Nat.Prime j : ℤ)) ≠ 0 := by
    intro h0
    have h1 : Nat.nth Nat.Prime j = k * Nat.nth Nat.Prime i := by
      have : ((Nat.nth Nat.Prime j : ℕ) : ℤ) = ((k * Nat.nth Nat.Prime i : ℕ) : ℤ) := by
        push_cast; linarith
      exact_mod_cast this
    have hdvd : Nat.nth Nat.Prime i ∣ Nat.nth Nat.Prime j := ⟨k, by rw [h1]; ring⟩
    exact hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)
  have key : (1 : ℝ) ≤ |(((k : ℤ) * (Nat.nth Nat.Prime i : ℤ) - (Nat.nth Nat.Prime j : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hz
  simpa using key

/-- For integers the condition makes `A` primitive (PROVED in Lean), the page's first remark: if `a i`
divided `a j` for `i ≠ j`, then `a j = k * a i` with `k ≥ 1`, and `|k * a i - a j| = 0 < 1`. -/
theorem erdos_problem_143.variants.integers_primitive {a : ℕ → ℕ} (ha_gt : ∀ i, 1 < a i)
    (h : ErdosSeparated (fun i => (a i : ℝ))) : ∀ i j, i ≠ j → ¬ a i ∣ a j := by
  intro i j hij hdvd
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · have := ha_gt j
      subst h0
      omega
    · exact h0
  have h1 : (1 : ℝ) ≤ |(k : ℝ) * (a i : ℝ) - (a j : ℝ)| := h i j hij k hk0
  have h2 : (k : ℝ) * (a i : ℝ) - (a j : ℝ) = 0 := by
    rw [hk]
    push_cast
    ring
  rw [h2, abs_zero] at h1
  norm_num at h1

/--
[Er35] (PROVED, not checked here): for a sequence of integers greater than `1`, none dividing another,
`∑ 1 / (b i * log (b i))` converges.
-/
theorem erdos_problem_143.variants.primitive_convergence :
    ∀ b : ℕ → ℕ, (∀ i, 1 < b i) → (∀ i j, i ≠ j → ¬ b i ∣ b j) →
      Summable (fun i => 1 / ((b i : ℝ) * Real.log (b i : ℝ))) :=
  sorry

/-- The integer case of the first question follows from [Er35] (PROVED in Lean from [Er35]): a separated
sequence of integers is primitive. -/
theorem erdos_problem_143.variants.integers_case_of_Er35
    (hEr35 : ∀ b : ℕ → ℕ, (∀ i, 1 < b i) → (∀ i j, i ≠ j → ¬ b i ∣ b j) →
      Summable (fun i => 1 / ((b i : ℝ) * Real.log (b i : ℝ))))
    (a : ℕ → ℕ) (ha_gt : ∀ i, 1 < a i) (ha_sep : ErdosSeparated (fun i => (a i : ℝ))) :
    Summable (fun i => 1 / ((a i : ℝ) * Real.log (a i : ℝ))) :=
  hEr35 a ha_gt (erdos_problem_143.variants.integers_primitive ha_gt ha_sep)

/--
The first question implies the second (PROVED in Lean): if `∑ 1 / (x log x)` converges, then
`∑_{x < n} 1 / x = o(log n)`. Split the sum at an index `m` so that the tail `∑_{i ≥ m} 1 / (a i log (a i))`
is below `ε / 2`. A term of the tail with `a i < n` satisfies `1 / a i = log (a i) * (1 / (a i log (a i)))
≤ log n * (1 / (a i log (a i)))`, and the first `m` terms add a constant. No separation is needed.
-/
theorem erdos_problem_143.variants.b_of_a (a : ℕ → ℝ) (ha_gt : ∀ i, 1 < a i)
    (hsum : Summable (fun i => 1 / (a i * Real.log (a i)))) :
    Tendsto
      (fun n : ℕ =>
        (∑' i, if a i < (n : ℝ) then 1 / a i else 0) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hlog : ∀ i, 0 < Real.log (a i) := fun i => Real.log_pos (ha_gt i)
  have hapos : ∀ i, 0 < a i := fun i => by linarith [ha_gt i]
  set f : ℕ → ℝ := fun i => 1 / (a i * Real.log (a i)) with hf
  have hfpos : ∀ i, 0 < f i := fun i => by
    have h1 := hlog i
    have h2 := hapos i
    simp only [hf]
    positivity
  set g : ℕ → ℕ → ℝ := fun n i => if a i < (n : ℝ) then 1 / a i else 0 with hg
  have hg_nonneg : ∀ n i, 0 ≤ g n i := fun n i => by
    have h2 := hapos i
    simp only [hg]
    split_ifs
    · positivity
    · exact le_rfl
  have hg_le_inv : ∀ n i, g n i ≤ 1 / a i := fun n i => by
    have h2 := hapos i
    simp only [hg]
    split_ifs
    · exact le_rfl
    · positivity
  have hg_le : ∀ n : ℕ, 1 ≤ n → ∀ i, g n i ≤ Real.log n * f i := by
    intro n hn i
    simp only [hg]
    split_ifs with h
    · have h1 : 1 / a i = Real.log (a i) * f i := by
        have h3 := (hlog i).ne'
        have h4 := (hapos i).ne'
        simp only [hf]
        field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_right (Real.log_le_log (hapos i) h.le) (hfpos i).le
    · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (hfpos i).le
  have hg_summable : ∀ n : ℕ, 1 ≤ n → Summable (g n) := fun n hn =>
    Summable.of_nonneg_of_le (hg_nonneg n) (hg_le n hn) (hsum.mul_left (Real.log n))
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun ε hε => ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 : 0 ≤ ∑' i, g n i := tsum_nonneg (hg_nonneg n)
    have hl : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    exact lt_of_lt_of_le hc (div_nonneg h0 hl)
  · obtain ⟨m, hm⟩ :=
      ((tendsto_sum_nat_add f).eventually (gt_mem_nhds (half_pos hε))).exists
    set C : ℝ := ∑ i ∈ Finset.range m, 1 / a i with hC
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => by have := hapos i; positivity)
    have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hlogtop.eventually_gt_atTop (2 * C / ε)] with n hn hn2
    have hlpos : 0 < Real.log n := lt_of_le_of_lt (by positivity) hn2
    have hsplit := (hg_summable n hn).sum_add_tsum_nat_add m
    have hhead : ∑ i ∈ Finset.range m, g n i ≤ C :=
      Finset.sum_le_sum (fun i _ => hg_le_inv n i)
    have hfm : Summable (fun k => f (k + m)) := (summable_nat_add_iff m).mpr hsum
    have hgm : Summable (fun k => g n (k + m)) := (summable_nat_add_iff m).mpr (hg_summable n hn)
    have htail : ∑' k, g n (k + m) ≤ Real.log n * (ε / 2) := by
      calc ∑' k, g n (k + m) ≤ ∑' k, Real.log n * f (k + m) :=
            Summable.tsum_le_tsum (fun k => hg_le n hn (k + m)) hgm (hfm.mul_left _)
        _ = Real.log n * ∑' k, f (k + m) := tsum_mul_left
        _ ≤ Real.log n * (ε / 2) := mul_le_mul_of_nonneg_left hm.le hlpos.le
    rw [div_lt_iff₀ hlpos]
    have h2C : 2 * C / ε * ε = 2 * C := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hn2 hε]

/--
Erdős's quantitative question (the page's second remark of this kind): `liminf |A ∩ [1,x]| / x = 0`.
It follows from [KLL25] (PROVED there, not checked here): if `|A ∩ [1,x]| ≥ c x` for all large `x` with
`c > 0`, then each block `[y, 4 y / c)` carries at least `c / 2` of `∑ 1 / x`, and `∑_{x < n} 1 / x` is at least
`c log n / (2 log (4 / c))` up to a constant, against the bound `o(log n)`. Upstream still records the
question as open.
-/
theorem erdos_problem_143.variants.liminf_density
    (a : ℕ → ℝ) (ha_inj : Function.Injective a) (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    liminf (fun x : ℝ => ((Set.range a ∩ Set.Icc 1 x).ncard : ℝ) / x) atTop = 0 :=
  sorry

/--
The "even" estimate suggested by Behrend's bound (OPEN for real sets; Behrend [Be35] proved it for primitive
sets of integers): `∑_{x < n, x ∈ A} 1 / x ≪ log n / √(log log n)`.
-/
theorem erdos_problem_143.variants.behrend_shape
    (a : ℕ → ℝ) (ha_inj : Function.Injective a) (ha_gt : ∀ i, 1 < a i)
    (ha_sep : ErdosSeparated a) :
    ∃ C : ℝ, ∀ n : ℕ, 3 ≤ n →
      (∑' i, if a i < (n : ℝ) then 1 / a i else 0) ≤
        C * (Real.log (n : ℝ) / Real.sqrt (Real.log (Real.log (n : ℝ)))) :=
  sorry

end
