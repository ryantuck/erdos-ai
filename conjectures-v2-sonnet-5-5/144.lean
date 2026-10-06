-- [AI - Claude Sonnet 5.5]: Erdős Problem 144 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Find
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

open Classical Filter Topology

noncomputable section

/-!
# Erdős Problem #144: Divisors that are close together

*Source:* [erdosproblems.com/144](https://www.erdosproblems.com/144) (banner **PROVED**, prize **\$250**:
"This has been solved in the affirmative."; page last edited 29 December 2025; two captures on 2026-02-20, the
page and its tidied problem box, with identical content). [Er61] [Er77c] [Er79] [Er79e] [ErGr80]
[Er81h, p.172] [Er82e] [Er85e] [Er97c] [Er98]

The density of integers which have two divisors $d_1,d_2$ such that $d_1<d_2<2d_1$ exists and is equal
to $1$.

Remarks recorded on the page:
* In [Er79] Erdős asks the stronger version with $2$ replaced by any constant $c>1$. The answer is yes (also
  to this stronger version), proved by Maier and Tenenbaum [MaTe84]. (Tenenbaum has told the page's author
  that they received \$650 for their solution.)
* In [Er64h] Erdős claimed a proof that the set of integers $n$ with divisors
  $d_1<d_2<d_1(1+(\log n)^{-\beta})$ has density $1$ if $\beta<\log 3-1$, but this claim was retracted in
  [ErHa79]. Erdős and Hall [ErHa79] proved that this set has density $0$ if $\beta>\log 3-1$ (in a stronger
  quantitative form). The proof of Maier and Tenenbaum [MaTe84] proves that the density is $1$ if
  $\beta<\log 3-1$.
* This is discussed in problem E3 of Guy's collection [Gu04]. See also [449] and [884].

Tags: number theory, divisors. OEIS: A005279. 2 comments at capture (not captured).

**Status.** PROVED [MaTe84]. The mirror (`teorth/erdosproblems`) has `proved` since 2025-08-31 and
`proved (Lean)` since 2026-08-24, with prize \$250. Upstream has no `144.lean`. The main theorem keeps its
`sorry`: the theorem of [MaTe84] is not in Mathlib.

**Encoding.**
* `HasCloseConsecutiveDivisors n` says that `n` has divisors `d₁ < d₂ < 2 * d₁`. For `n ≥ 1` a divisor is
  positive, and `d₁ = 0` could not occur anyway, since `d₂ < 2 * 0` is false. The word "Consecutive" in the
  name is harmless: `variants.consecutive_iff` shows that a close pair exists iff a close pair with no divisor
  of `n` strictly between them exists.
* The count `A(N)` is `((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card`, the
  number of `m ∈ {1, …, N}` with the property. `open Classical` supplies the decidability of the filter.
  `variants.bounded_iff` gives a decidable form with `Nat.divisors`, and `variants.count_thirty` uses it to
  check `A(30) = 8` (the numbers `6, 12, 15, 18, 20, 24, 28, 30`).
* The convergence $A(N)/N\to1$ is extremely slow. A sieve gives $A(10^3)/10^3=0.392$, $A(10^6)/10^6=0.476$ and
  $A(10^7)/10^7=0.491$, so the density cannot be read off a finite computation.
* `HasDivisorsWithin r n` is the same property with the bound `d₂ < r * d₁` for a real `r`.
  `variants.hasClose_iff_within_two` is the case `r = 2`. `variants.generalized` is the version for every
  `c > 1` asked in [Er79] and proved in [MaTe84], and `variants.main_of_generalized` shows that it implies the
  main theorem.
* `variants.beta_lt` and `variants.beta_gt` are the two $\beta$ statements of the second remark, with the
  natural logarithm (the threshold $\log 3-1\approx0.0986$ is positive), for the divisor bound
  `d₂ < d₁ * (1 + (log n) ^ (-β))`.

## References

* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961), 221–254.
* [Er64h] Erdős, P., _On some applications of probability to analysis and number theory_. J. London Math. Soc.
  (1964), 692–696.
* [Er77c] Erdős, P., _Problems and results on combinatorial number theory. III_. In: Number theory day
  (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.
* [Er79] Erdős, P., _Some unconventional problems in number theory_. Math. Mag. (1979), 67–70.
* [ErHa79] Erdős, P. and Hall, R. R., _The propinquity of divisors_. Bull. London Math. Soc. (1979), 304–307.
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_.
  Monographies de L'Enseignement Mathématique (1980).
* [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_. In: Analytic
  number theory (Philadelphia, Pa., 1980) (1981), 171–182. The page cites p. 172.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982), 59–79.
  **DEFERRED:** the venue was not recovered.
* [MaTe84] Maier, H. and Tenenbaum, G., _On the set of divisors of an integer_. Invent. Math. (1984), 121–128.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Er98] Erdős, P., _Some of my new and almost new problems and results in combinatorial number theory_.
  In: Number theory (Eger, 1996) (1998), 169–180.
* [Gu04] Guy, R. K., _Unsolved problems in number theory_ (2004), xviii+437.
* [Er79e], [Er85e] cited on the page. **DEFERRED:** no bibliographic data was recovered.
* [449], [884] The page's cross-references to Problems 449 and 884.

(Provenance: [Er64h], [Er79], [ErHa79], [MaTe84] and [Gu04] are from the `/latex/144` fetch in the session
logs. [Er61], [Er77c], [ErGr80], [Er81h], [Er82e], [Er97c] and [Er98] are from the bibliographies of the
`/latex` pages of other problems.)
-/

/-- A positive integer n has two divisors d₁, d₂ with d₁ < d₂ < 2 * d₁. -/
def HasCloseConsecutiveDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/--
Erdős Problem #144 [Er61, Er77c, Er79, Er79e, ErGr80, Er81h, Er82e, Er85e, Er97c, Er98] — PROVED (\$250):
The density of integers which have two divisors d₁, d₂ such that d₁ < d₂ < 2*d₁
exists and is equal to 1.

Formally, writing A(N) for the number of integers n with 1 ≤ n ≤ N which have
two divisors d₁ < d₂ < 2*d₁, A(N)/N → 1 as N → ∞.

Proved by Maier and Tenenbaum [MaTe84] (not checked here).
-/
theorem erdos_problem_144 :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card : ℝ) /
        (N : ℝ))
      atTop
      (𝓝 (1 : ℝ)) :=
  sorry

/-- `n` has two divisors `d₁ < d₂` with `d₂ < r * d₁`, for a real bound `r`. -/
def HasDivisorsWithin (r : ℝ) (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ (d₂ : ℝ) < r * d₁

/-- The case `r = 2` of `HasDivisorsWithin` is the property of the main theorem (PROVED in Lean). -/
theorem erdos_problem_144.variants.hasClose_iff_within_two (n : ℕ) :
    HasCloseConsecutiveDivisors n ↔ HasDivisorsWithin 2 n := by
  unfold HasCloseConsecutiveDivisors HasDivisorsWithin
  constructor
  · rintro ⟨d₁, d₂, h1, h2, h3, h4⟩
    exact ⟨d₁, d₂, h1, h2, h3, by exact_mod_cast h4⟩
  · rintro ⟨d₁, d₂, h1, h2, h3, h4⟩
    exact ⟨d₁, d₂, h1, h2, h3, by exact_mod_cast h4⟩

/--
The page's stronger version of [Er79] (PROVED by Maier and Tenenbaum [MaTe84], not checked here): for every
`c > 1` the density of integers with two divisors `d₁ < d₂ < c * d₁` exists and is `1`.
-/
theorem erdos_problem_144.variants.generalized (c : ℝ) (hc : 1 < c) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasDivisorsWithin c (n + 1))).card : ℝ) / (N : ℝ))
      atTop (𝓝 (1 : ℝ)) :=
  sorry

/-- The stronger version implies the main theorem (PROVED in Lean), by the case `c = 2`. -/
theorem erdos_problem_144.variants.main_of_generalized
    (h : ∀ c : ℝ, 1 < c →
      Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun n => HasDivisorsWithin c (n + 1))).card : ℝ) / (N : ℝ))
        atTop (𝓝 (1 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card : ℝ) /
        (N : ℝ))
      atTop
      (𝓝 (1 : ℝ)) := by
  have h2 := h 2 (by norm_num)
  have hfun : (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card : ℝ) /
        (N : ℝ)) =
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasDivisorsWithin 2 (n + 1))).card : ℝ) / (N : ℝ)) := by
    funext N
    rw [Finset.filter_congr (fun n _ => erdos_problem_144.variants.hasClose_iff_within_two (n + 1))]
  rw [hfun]
  exact h2

/--
The Maier–Tenenbaum half of the page's second remark (PROVED [MaTe84], not checked here): if
`β < log 3 - 1`, the set of `n` with divisors `d₁ < d₂ < d₁ * (1 + (log n) ^ (-β))` has density `1`.
-/
theorem erdos_problem_144.variants.beta_lt (β : ℝ) (hβ : β < Real.log 3 - 1) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter
            (fun n => HasDivisorsWithin (1 + Real.log ((n + 1 : ℕ) : ℝ) ^ (-β)) (n + 1))).card : ℝ) /
          (N : ℝ))
      atTop (𝓝 (1 : ℝ)) :=
  sorry

/--
The Erdős–Hall half of the page's second remark (PROVED [ErHa79], not checked here): if `β > log 3 - 1`,
the same set has density `0`.
-/
theorem erdos_problem_144.variants.beta_gt (β : ℝ) (hβ : Real.log 3 - 1 < β) :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter
            (fun n => HasDivisorsWithin (1 + Real.log ((n + 1 : ℕ) : ℝ) ^ (-β)) (n + 1))).card : ℝ) /
          (N : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
  sorry

/-- A decidable form of the property (PROVED in Lean): for `n ≥ 1` both divisors lie in `Nat.divisors n`. -/
theorem erdos_problem_144.variants.bounded_iff {n : ℕ} (hn : 0 < n) :
    HasCloseConsecutiveDivisors n ↔
      ∃ d₁ ∈ n.divisors, ∃ d₂ ∈ n.divisors, d₁ < d₂ ∧ d₂ < 2 * d₁ := by
  unfold HasCloseConsecutiveDivisors
  constructor
  · rintro ⟨d₁, d₂, h1, h2, h3, h4⟩
    exact ⟨d₁, Nat.mem_divisors.mpr ⟨h1, hn.ne'⟩, d₂, Nat.mem_divisors.mpr ⟨h2, hn.ne'⟩, h3, h4⟩
  · rintro ⟨d₁, h1, d₂, h2, h3, h4⟩
    exact ⟨d₁, d₂, (Nat.mem_divisors.mp h1).1, (Nat.mem_divisors.mp h2).1, h3, h4⟩

/--
`A(30) = 8` for the count in the main theorem (PROVED in Lean by a finite check): the integers `m ≤ 30` with
two divisors `d₁ < d₂ < 2 * d₁` are `6, 12, 15, 18, 20, 24, 28, 30`. This checks the encoding of the count,
including the shift `n + 1`.
-/
theorem erdos_problem_144.variants.count_thirty :
    ((Finset.range 30).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card = 8 := by
  have h : (Finset.range 30).filter (fun n => HasCloseConsecutiveDivisors (n + 1)) =
      (Finset.range 30).filter
        (fun n => ∃ d₁ ∈ (n + 1).divisors, ∃ d₂ ∈ (n + 1).divisors, d₁ < d₂ ∧ d₂ < 2 * d₁) := by
    apply Finset.filter_congr
    intro n _
    exact erdos_problem_144.variants.bounded_iff (Nat.succ_pos n)
  rw [h]
  decide

/--
"Consecutive" in the name is harmless (PROVED in Lean): `n` has two divisors `d₁ < d₂ < 2 * d₁` iff it has two
such divisors with no divisor of `n` strictly between them. Take a pair with `d₂ - d₁` minimal.
-/
theorem erdos_problem_144.variants.consecutive_iff (n : ℕ) :
    HasCloseConsecutiveDivisors n ↔
      ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁ ∧
        ∀ e : ℕ, e ∣ n → d₁ < e → e < d₂ → False := by
  constructor
  · rintro ⟨d₁, d₂, h1, h2, h3, h4⟩
    have hex : ∃ k, ∃ a b : ℕ, a ∣ n ∧ b ∣ n ∧ a < b ∧ b < 2 * a ∧ b - a = k :=
      ⟨d₂ - d₁, d₁, d₂, h1, h2, h3, h4, rfl⟩
    obtain ⟨a, b, ha, hb, hab, hb2, hk⟩ := Nat.find_spec hex
    refine ⟨a, b, ha, hb, hab, hb2, fun e he h1 h2 => ?_⟩
    have hlt : e - a < Nat.find hex := by omega
    exact Nat.find_min hex hlt ⟨a, e, ha, he, h1, by omega, rfl⟩
  · rintro ⟨d₁, d₂, h1, h2, h3, h4, -⟩
    exact ⟨d₁, d₂, h1, h2, h3, h4⟩

end
