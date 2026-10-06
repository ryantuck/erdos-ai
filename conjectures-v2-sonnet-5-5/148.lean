-- [AI - Claude Sonnet 5.5]: Erdős Problem 148 — second-pass formalization
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open BigOperators Real Filter

/-!
# Erdős Problem #148: The number of representations of 1 as a sum of $k$ distinct unit fractions

*Source:* [erdosproblems.com/148](https://www.erdosproblems.com/148) (banner **OPEN**: "This is open, and
cannot be resolved with a finite computation."; page last edited 27 September 2025; captured 2026-02-20 as the
tidied problem box). [ErGr80, p. 32]

Let $F(k)$ be the number of solutions to $1 = \frac{1}{n_1}+\cdots+\frac{1}{n_k}$, where
$1\leq n_1<\cdots<n_k$ are distinct integers. Find good estimates for $F(k)$.

Remarks recorded on the page:
* The current best bounds known are
  $2^{c^{\frac{k}{\log k}}}\leq F(k) \leq c_0^{(\frac{1}{5}+o(1))2^k}$, where $c>0$ is some absolute constant
  and $c_0=1.26408\cdots$ is the 'Vardi constant'. The lower bound is due to Konyagin [Ko14] and the upper
  bound to Elsholtz and Planitzer [ElPl21].

Tags: number theory, unit fractions. OEIS: A076393, A006585. 2 comments at capture (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31, no prize. Upstream has
`erdos_148 : F =Θ[atTop] answer(sorry)`, category `research open`, and the two bounds as `research solved`
variants (`lower_bound` in Konyagin's explicit form, `upper_bound` with the constant of [ElPl21]).

**What the first pass got wrong, and what this file does.**
* *The main theorem is a guess that is not on the page.* The page says "Find good estimates for $F(k)$", and
  records the gap $2^{c^{k/\log k}}\le F(k)\le c_0^{(1/5+o(1))2^k}$. The first pass states that
  $c_1^{2^k}\le F(k)\le c_2^{2^k}$. Its upper half is the known bound, and its lower half is a conjecture that
  nothing on the page makes (the known lower bound is far smaller). It is kept as `variants.first_pass_guess`,
  OPEN and editorial, with `variants.first_pass_guess_of_lower` showing that, given the upper bound, it is
  equivalent to its lower half. The main theorem is now the request of the page, read as in upstream: the
  order of magnitude of $F(k)$ is a closed form, `IsExpLog` (the class of `142.lean`). That class is an editorial
  choice.
* *The Konyagin variant is trivially true as written.* `egyptianFractionCount_konyagin_lower_bound` says
  `∃ c > 0, 2 ^ (c ^ (k / log k)) ≤ F k`. For $c\le1$ the left side is at most $2$, so the statement follows from
  $F(k)\ge2$ (`variants.konyagin_first_pass_of_two_le`). The page's $c$ must exceed $1$, for the bound to be a double
  exponential. v2 has `1 < c`. `variants.konyagin_of_explicit` shows that this follows from the explicit form
  of [Ko14, Theorem 1] that upstream records.
* *The constant of the upper bound.* The page and the first pass print $c_0=1.26408\cdots$, the Vardi constant
  $E$. Upstream, reading [ElPl21, Remark 3], has $c_0=\lim u_n^{2^{-n}}=1.5979\cdots=E^2$, for the sequence
  $u=1,2,6,42,1806,\dots$. A computation confirms both numbers (Addendum of the review), and the exponent with
  $E$ would be half of the one with $E^2$. The first pass avoids the issue by asking only for some `c₀ > 1`, which
  is much weaker than the cited bound. v2 keeps that form and adds `variants.upper_bound_precise` with
  $c_0=E^2$. **DEFERRED:** which constant the paper states was not checked.

**Encoding.**
* `egyptianFractionCount k` is `Set.ncard` of the set of `k`-element sets of positive integers whose
  reciprocals sum to `1`, which is the number of increasing sequences. `Set.ncard` of an infinite set would be
  `0`, so finiteness matters: `finite_solutions` proves in Lean that for every `k` and every rational target the
  set of solutions is finite (the least element is at most `k` divided by the target). So the count is the true
  count for every `k`.
* `variants.F_one`, `variants.F_two` and `variants.F_three` prove `F 1 = 1`, `F 2 = 0` and `F 3 = 1` (the only
  solution for $k=3$ is $\{2,3,6\}$). A search (Addendum of the review) gives $F(k)=1,0,1,6,72,2320,245765$ for
  $k\le7$, the values of A006585.
* The asymptotics use `∀ᶠ k in atTop`. At `k = 0, 1` the quotient `k / log k` is junk and is ignored.

## References

* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_.
  Monographies de L'Enseignement Mathématique (1980). The page cites p. 32.
* [Ko14] Konyagin, S. V., _Double exponential lower bound for the number of representations of unity by
  Egyptian fractions_. Math. Notes (2014), 277–281.
* [ElPl21] Elsholtz, C. and Planitzer, S., _Sums of four and more unit fractions and approximate
  parametrizations_. Bull. Lond. Math. Soc. (2021), 695–709. **DEFERRED:** whether this is the paper that the
  page cites. Another paper of the same authors, "The number of solutions of the Erdős–Straus equation and sums
  of $k$ unit fractions" (Proc. R. Soc. Edinb. A), also exists.

(Provenance: [ErGr80] is from the bibliographies of the `/latex` pages of other problems. [Ko14] and [ElPl21] are
from the docstrings of upstream `148.lean`. **DEFERRED:** no `/latex/148` fetch exists in the logs, so the
entries were not checked against the page's own bibliography.)
-/

/-- F(k) is the number of k-element sets of positive integers
    whose unit fractions sum to 1: 1/n₁ + ⋯ + 1/nₖ = 1. -/
noncomputable def egyptianFractionCount (k : ℕ) : ℕ :=
  Set.ncard {S : Finset ℕ | S.card = k ∧ (∀ n ∈ S, 0 < n) ∧
    ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1}

/-- Konyagin lower bound [Ko14]:
    There exists an absolute constant c > 1 such that
    2^{c^{k/log k}} ≤ F(k) for all sufficiently large k. (The first pass had `0 < c`, which makes the
    statement trivial: see `erdos_problem_148.variants.konyagin_first_pass_of_two_le`.) -/
theorem egyptianFractionCount_konyagin_lower_bound :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (c ^ ((k : ℝ) / Real.log k)) ≤
        (egyptianFractionCount k : ℝ) :=
  sorry

/-- Elsholtz–Planitzer upper bound [ElPl21]:
    There exists a constant c₀ > 1 (the Vardi constant, c₀ ≈ 1.26408) such that
    for every ε > 0, F(k) ≤ c₀^{(1/5 + ε)·2^k} for all sufficiently large k. -/
theorem egyptianFractionCount_elsholtz_planitzer_upper_bound :
    ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (egyptianFractionCount k : ℝ) ≤
        c₀ ^ ((1 / 5 + ε) * (2 : ℝ) ^ (k : ℕ)) :=
  sorry

/--
The closed forms: functions built from constants and the identity by sums, products, reciprocals,
`exp` and `log`. As in `142.lean`, an "estimate" is read as an order of magnitude given by such a function.
-/
inductive IsExpLog : (ℝ → ℝ) → Prop
  | const (c : ℝ) : IsExpLog (fun _ => c)
  | id : IsExpLog (fun x => x)
  | add {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x + g x)
  | mul {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x * g x)
  | inv {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => (f x)⁻¹)
  | exp {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.exp (f x))
  | log {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.log (f x))

/-- Erdős Problem #148 [ErGr80, p.32] — OPEN:
    Find good estimates for F(k), the number of representations of 1
    as a sum of exactly k distinct unit fractions.

    The page records the gap 2^{c^{k/log k}} ≤ F(k) ≤ c₀^{(1/5 + o(1))·2^k} between the bounds of Konyagin [Ko14]
    and Elsholtz–Planitzer [ElPl21]. The request is read here, as upstream reads it, as the order of
    magnitude of F(k): there is a closed-form function f (built from constants and the identity by sums,
    products, reciprocals, exp and log) and constants c, C > 0 with c · f(k) ≤ F(k) ≤ C · f(k) for all large k.
    The class of closed forms is an editorial choice. The first pass's guess that F(k) is exponential in
    2^k is `variants.first_pass_guess`. -/
theorem erdos_problem_148 :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ (∀ᶠ k : ℕ in atTop, 0 < f k) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ k : ℕ in atTop,
        c * f k ≤ (egyptianFractionCount k : ℝ) ∧ (egyptianFractionCount k : ℝ) ≤ C * f k :=
  sorry

/--
The first pass's guess (OPEN, editorial; it is not on the page): `F(k)` is exponential in `2 ^ k`, that is,
`c₁ ^ (2 ^ k) ≤ F(k) ≤ c₂ ^ (2 ^ k)` for large `k`. Its upper half is the known bound of [ElPl21]. Its lower half
would improve the bound of [Ko14], which is far smaller, to match.
-/
theorem erdos_problem_148.variants.first_pass_guess :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ 1 < c₂ ∧ ∀ᶠ k : ℕ in atTop,
      c₁ ^ ((2 : ℝ) ^ (k : ℕ)) ≤ (egyptianFractionCount k : ℝ) ∧
      (egyptianFractionCount k : ℝ) ≤ c₂ ^ ((2 : ℝ) ^ (k : ℕ)) :=
  sorry

/--
Given the upper bound of [ElPl21], the first pass's guess is equivalent to its lower half (PROVED in Lean, one
direction shown, which is the one that matters): the upper bound with `c₂ = c₀ ^ (6 / 5)` is the case `ε = 1`.
-/
theorem erdos_problem_148.variants.first_pass_guess_of_lower
    (hup : ∃ c₀ : ℝ, 1 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      (egyptianFractionCount k : ℝ) ≤ c₀ ^ ((1 / 5 + ε) * (2 : ℝ) ^ (k : ℕ)))
    (hlow : ∃ c₁ : ℝ, 1 < c₁ ∧ ∀ᶠ k : ℕ in atTop,
      c₁ ^ ((2 : ℝ) ^ (k : ℕ)) ≤ (egyptianFractionCount k : ℝ)) :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ 1 < c₂ ∧ ∀ᶠ k : ℕ in atTop,
      c₁ ^ ((2 : ℝ) ^ (k : ℕ)) ≤ (egyptianFractionCount k : ℝ) ∧
      (egyptianFractionCount k : ℝ) ≤ c₂ ^ ((2 : ℝ) ^ (k : ℕ)) := by
  obtain ⟨c₀, hc₀, hup'⟩ := hup
  obtain ⟨c₁, hc₁, hlow'⟩ := hlow
  refine ⟨c₁, c₀ ^ ((6 : ℝ) / 5), hc₁, Real.one_lt_rpow hc₀ (by norm_num), ?_⟩
  filter_upwards [hlow', hup' 1 one_pos] with k hl hu
  refine ⟨hl, ?_⟩
  have h2 : c₀ ^ ((1 / 5 + 1) * (2 : ℝ) ^ (k : ℕ)) =
      (c₀ ^ ((6 : ℝ) / 5)) ^ ((2 : ℝ) ^ (k : ℕ)) := by
    rw [← Real.rpow_mul (by linarith)]
    norm_num
  rw [← h2]
  exact hu

/--
The first pass's Konyagin statement, with `0 < c`, is trivially true (PROVED in Lean): it follows from
`F(k) ≥ 2` for large `k`, with `c = 1`, since then the left side is `2 ^ 1 = 2`. (`F(k) ≥ 2` holds for `k ≥ 4`:
`F(4) = 6`, and splitting the largest denominator `m` into `m + 1` and `m * (m + 1)` is an injection from the
solutions with `k` terms into those with `k + 1` terms.)
-/
theorem erdos_problem_148.variants.konyagin_first_pass_of_two_le
    (h : ∀ᶠ k : ℕ in atTop, 2 ≤ egyptianFractionCount k) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (c ^ ((k : ℝ) / Real.log k)) ≤ (egyptianFractionCount k : ℝ) := by
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [h] with k hk
  rw [Real.one_rpow, Real.rpow_one]
  exact_mod_cast hk

/--
Konyagin's explicit form [Ko14, Theorem 1] (PROVED, not checked here), as upstream records it:
`F(k) ≥ exp (exp ((log 2 * log 3 / 3 + o(1)) * k / log k))`.
-/
theorem erdos_problem_148.variants.konyagin_explicit :
    ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ k : ℕ in atTop,
      Real.exp (Real.exp ((Real.log 2 * Real.log 3 / 3 + o k) * ((k : ℝ) / Real.log k))) ≤
        (egyptianFractionCount k : ℝ) :=
  sorry

/--
The explicit form of [Ko14] gives the repaired Konyagin variant, with `c = exp (log 2 * log 3 / 6) > 1` (PROVED in
Lean): `2 ^ (c ^ x) = exp (log 2 * exp (a x / 2))` is at most `exp (exp ((a + o) x))` once `o > -a / 2`, because
`log 2 ≤ 1`.
-/
theorem erdos_problem_148.variants.konyagin_of_explicit
    (h : ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ k : ℕ in atTop,
      Real.exp (Real.exp ((Real.log 2 * Real.log 3 / 3 + o k) * ((k : ℝ) / Real.log k))) ≤
        (egyptianFractionCount k : ℝ)) :
    ∃ c : ℝ, 1 < c ∧ ∀ᶠ k : ℕ in atTop,
      (2 : ℝ) ^ (c ^ ((k : ℝ) / Real.log k)) ≤ (egyptianFractionCount k : ℝ) := by
  obtain ⟨o, ho, hev⟩ := h
  set a : ℝ := Real.log 2 * Real.log 3 / 3 with ha
  have ha0 : 0 < a := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  refine ⟨Real.exp (a / 2), Real.one_lt_exp_iff.mpr (by linarith), ?_⟩
  have ho' : ∀ᶠ k : ℕ in atTop, -(a / 2) < o k := (tendsto_order.1 ho).1 _ (by linarith)
  filter_upwards [hev, ho', eventually_ge_atTop 1] with k hk hok hk1
  have hx : 0 ≤ (k : ℝ) / Real.log k :=
    div_nonneg (Nat.cast_nonneg k) (Real.log_nonneg (by exact_mod_cast hk1))
  set x : ℝ := (k : ℝ) / Real.log k with hxdef
  have h1 : (Real.exp (a / 2)) ^ x = Real.exp (a / 2 * x) := (Real.exp_mul _ _).symm
  have h2 : (2 : ℝ) ^ ((Real.exp (a / 2)) ^ x) =
      Real.exp (Real.log 2 * Real.exp (a / 2 * x)) := by
    rw [h1, Real.rpow_def_of_pos (by norm_num)]
  rw [h2]
  refine le_trans (Real.exp_le_exp.mpr ?_) hk
  have h3 : Real.exp ((a + o k) * x) =
      Real.exp (a / 2 * x) * Real.exp ((a / 2 + o k) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : 1 ≤ Real.exp ((a / 2 + o k) * x) :=
    Real.one_le_exp (mul_nonneg (by linarith) hx)
  have h5 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h6 : 0 < Real.exp (a / 2 * x) := Real.exp_pos _
  rw [h3]
  calc Real.log 2 * Real.exp (a / 2 * x) ≤ 1 * Real.exp (a / 2 * x) :=
        mul_le_mul_of_nonneg_right h5 h6.le
    _ = Real.exp (a / 2 * x) := one_mul _
    _ ≤ Real.exp (a / 2 * x) * Real.exp ((a / 2 + o k) * x) := le_mul_of_one_le_right h6.le h4

/-- The sequence `u₀ = 1`, `u_{n+1} = u_n * (u_n + 1)`: `1, 2, 6, 42, 1806, …`, Sylvester's sequence minus one. -/
def erdos_problem_148.u : ℕ → ℕ
  | 0 => 1
  | n + 1 => erdos_problem_148.u n * (erdos_problem_148.u n + 1)

/--
The constant `c₀ = lim u_n ^ (2 ^ (-n)) = 1.5979…` of [ElPl21], as upstream reads it (Corollary 3 and Remark 3):
the sequence `u_n ^ (2 ^ (-n))` increases to `c₀`, so the limit is the supremum. It is the square of the Vardi
constant `1.26408…`. A computation up to `n = 14` gives `1.5979102180318732`.
-/
noncomputable def erdos_problem_148.c₀ : ℝ :=
  ⨆ n : ℕ, (erdos_problem_148.u n : ℝ) ^ ((1 : ℝ) / 2 ^ n)

/--
The upper bound of [ElPl21] with the constant `c₀ = 1.5979…` (PROVED, not checked here; the exponent
`(2/5 + ε) 2 ^ (k-1)` of [ElPl21, Corollary 3] is `(1/5 + ε/2) 2 ^ k`). The page's `1.26408…` is the square root
of this constant, and would give half the exponent. **DEFERRED:** which constant the paper states.
-/
theorem erdos_problem_148.variants.upper_bound_precise :
    ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ k : ℕ in atTop,
      (egyptianFractionCount k : ℝ) ≤ erdos_problem_148.c₀ ^ ((1 / 5 + o k) * (2 : ℝ) ^ (k : ℕ)) :=
  sorry

/--
For every `k` and every rational target `r`, there are only finitely many `k`-element sets of positive integers
whose reciprocals sum to `r` (PROVED in Lean). So `Set.ncard` in `egyptianFractionCount` is the true count, and
not the junk value `0` of an infinite set. The least element `m` of a solution satisfies `m ≤ k / r`, since all
`k` terms are at most `1 / m`, and the rest is a solution with `k - 1` terms for the target `r - 1 / m`.
-/
theorem erdos_problem_148.finite_solutions (k : ℕ) (r : ℚ) :
    {S : Finset ℕ | S.card = k ∧ (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = r}.Finite := by
  induction k generalizing r with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton (∅ : Finset ℕ)) ?_
    intro S hS
    simp only [Set.mem_setOf_eq, Finset.card_eq_zero] at hS
    simp [hS.1]
  | succ k ih =>
    by_cases hr : 0 < r
    · set B : ℕ := ⌊((k + 1 : ℕ) : ℚ) / r⌋₊ with hB
      have hcover : {S : Finset ℕ | S.card = k + 1 ∧ (∀ n ∈ S, 0 < n) ∧
          ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = r} ⊆
          ⋃ m ∈ Finset.range (B + 1), (fun T : Finset ℕ => insert m T) ''
            {T : Finset ℕ | T.card = k ∧ (∀ n ∈ T, 0 < n) ∧
              ∑ n ∈ T, (1 : ℚ) / (n : ℚ) = r - 1 / (m : ℚ)} := by
        intro S hS
        obtain ⟨hcard, hpos, hsum⟩ := hS
        have hne : S.Nonempty := by
          rw [← Finset.card_pos]
          omega
        set m := S.min' hne with hm
        have hmS : m ∈ S := Finset.min'_mem S hne
        have hmpos : 0 < m := hpos m hmS
        have hle : ∀ n ∈ S, (1 : ℚ) / (n : ℚ) ≤ 1 / (m : ℚ) := by
          intro n hn
          have hmn : m ≤ n := Finset.min'_le S n hn
          exact one_div_le_one_div_of_le (by exact_mod_cast hmpos) (by exact_mod_cast hmn)
        have hsum_le : r ≤ ((k + 1 : ℕ) : ℚ) * (1 / (m : ℚ)) := by
          rw [← hsum]
          calc ∑ n ∈ S, (1 : ℚ) / (n : ℚ) ≤ ∑ n ∈ S, (1 : ℚ) / (m : ℚ) := Finset.sum_le_sum hle
            _ = ((k + 1 : ℕ) : ℚ) * (1 / (m : ℚ)) := by
              rw [Finset.sum_const, hcard]
              simp
        have hmle : m ≤ B := by
          rw [hB]
          apply Nat.le_floor
          rw [le_div_iff₀ hr]
          have hm0 : (0 : ℚ) < m := by exact_mod_cast hmpos
          have : r * (m : ℚ) ≤ ((k + 1 : ℕ) : ℚ) := by
            have := mul_le_mul_of_nonneg_right hsum_le hm0.le
            rwa [mul_assoc, one_div, inv_mul_cancel₀ hm0.ne', mul_one] at this
          linarith
        simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Finset.mem_range]
        refine ⟨m, by omega, S.erase m, ⟨?_, ?_, ?_⟩, Finset.insert_erase hmS⟩
        · rw [Finset.card_erase_of_mem hmS, hcard]
          rfl
        · intro n hn
          exact hpos n (Finset.mem_of_mem_erase hn)
        · have := Finset.add_sum_erase S (fun n => (1 : ℚ) / (n : ℚ)) hmS
          linarith
      refine Set.Finite.subset ?_ hcover
      refine Set.Finite.biUnion (s := ((Finset.range (B + 1) : Finset ℕ) : Set ℕ))
        (Finset.finite_toSet _) (fun m _ => ?_)
      exact (ih _).image _
    · refine Set.Finite.subset (Set.finite_empty) ?_
      intro S hS
      obtain ⟨hcard, hpos, hsum⟩ := hS
      exfalso
      have hne : S.Nonempty := by
        rw [← Finset.card_pos]
        omega
      have : 0 < ∑ n ∈ S, (1 : ℚ) / (n : ℚ) :=
        Finset.sum_pos (fun n hn => by have := hpos n hn; positivity) hne
      rw [hsum] at this
      exact hr this

/-- `F 1 = 1`: the only representation with one unit fraction is `1 = 1 / 1` (PROVED in Lean). -/
theorem erdos_problem_148.variants.F_one : egyptianFractionCount 1 = 1 := by
  have h : {S : Finset ℕ | S.card = 1 ∧ (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1} =
      {{1}} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Finset.card_eq_one]
    constructor
    · rintro ⟨⟨a, rfl⟩, -, hsum⟩
      simp only [Finset.sum_singleton, one_div, inv_eq_one, Nat.cast_eq_one] at hsum
      rw [hsum]
    · rintro rfl
      exact ⟨⟨1, rfl⟩, by simp, by simp⟩
  unfold egyptianFractionCount
  rw [h, Set.ncard_singleton]

/-- Two distinct unit fractions never sum to `1`: the smaller denominator is `1` or at least `2`. -/
theorem erdos_problem_148.two_aux {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (h : (1 : ℚ) / a + 1 / b = 1) : False := by
  have hb : 0 < b := by omega
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rcases Nat.lt_or_ge a 2 with h1 | h2
  · have : a = 1 := by omega
    subst this
    have : (0 : ℚ) < 1 / b := by positivity
    simp only [Nat.cast_one, div_one] at h
    linarith
  · have h3 : (1 : ℚ) / a ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h2)
    have h4 : (1 : ℚ) / b ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 3 ≤ b))
    linarith

/-- `F 2 = 0`: no two distinct unit fractions sum to `1` (PROVED in Lean). -/
theorem erdos_problem_148.variants.F_two : egyptianFractionCount 2 = 0 := by
  have h : {S : Finset ℕ | S.card = 2 ∧ (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1} =
      ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hcard, hpos, hsum⟩
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    rw [Finset.sum_pair hab] at hsum
    have ha : 0 < a := hpos a (by simp)
    have hb : 0 < b := hpos b (by simp)
    rcases lt_or_gt_of_ne hab with h1 | h1
    · exact erdos_problem_148.two_aux ha h1 hsum
    · exact erdos_problem_148.two_aux hb h1 (by linarith)
  unfold egyptianFractionCount
  rw [h, Set.ncard_empty]

/-- The only increasing solution of `1 / a + 1 / b + 1 / c = 1` is `(2, 3, 6)`. -/
theorem erdos_problem_148.three_aux {a b c : ℕ} (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h : (1 : ℚ) / a + 1 / b + 1 / c = 1) : a = 2 ∧ b = 3 ∧ c = 6 := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  have hc' : (0 : ℚ) < c := by exact_mod_cast hc
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have ha' : (0 : ℚ) < a := by exact_mod_cast ha
  have ha2 : 2 ≤ a := by
    by_contra hlt
    have : a = 1 := by omega
    subst this
    have : (0 : ℚ) < 1 / b := by positivity
    have : (0 : ℚ) < 1 / c := by positivity
    simp only [Nat.cast_one, div_one] at h
    linarith
  have ha3 : a < 3 := by
    by_contra hge
    have h3 : (1 : ℚ) / a ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 3 ≤ a))
    have h4 : (1 : ℚ) / b ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 4 ≤ b))
    have h5 : (1 : ℚ) / c ≤ 1 / 5 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 5 ≤ c))
    linarith
  have ha_eq : a = 2 := by omega
  subst ha_eq
  have hb3 : b < 4 := by
    by_contra hge
    have h4 : (1 : ℚ) / b ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 4 ≤ b))
    have h5 : (1 : ℚ) / c ≤ 1 / 5 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (by omega : 5 ≤ c))
    push_cast at h
    linarith
  have hb_eq : b = 3 := by omega
  subst hb_eq
  have hc6 : (1 : ℚ) / c = 1 / 6 := by
    norm_num at h ⊢
    linarith
  have : (c : ℚ) = 6 := by
    have := congrArg (fun x : ℚ => 1 / x) hc6
    simpa using this
  refine ⟨rfl, rfl, ?_⟩
  exact_mod_cast this

/-- `F 3 = 1`: the only representation of `1` with three distinct unit fractions is `1 = 1/2 + 1/3 + 1/6`
(PROVED in Lean). -/
theorem erdos_problem_148.variants.F_three : egyptianFractionCount 3 = 1 := by
  have h : {S : Finset ℕ | S.card = 3 ∧ (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 : ℚ) / (n : ℚ) = 1} =
      {{2, 3, 6}} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hcard, hpos, hsum⟩
      obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hcard
      have hx : 0 < x := hpos x (by simp)
      have hy : 0 < y := hpos y (by simp)
      have hz : 0 < z := hpos z (by simp)
      rw [Finset.sum_insert (by simp [hxy, hxz]), Finset.sum_insert (by simp [hyz]),
        Finset.sum_singleton] at hsum
      rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
        rcases lt_or_gt_of_ne hyz with h3 | h3
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hx h1 h3 (by linarith)
        subst e1 e2 e3
        decide
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hx h2 h3 (by linarith)
        subst e1 e2 e3
        decide
      · omega
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hz h2 h1 (by linarith)
        subst e1 e2 e3
        decide
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hy h1 h2 (by linarith)
        subst e1 e2 e3
        decide
      · omega
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hy h3 h2 (by linarith)
        subst e1 e2 e3
        decide
      · obtain ⟨e1, e2, e3⟩ := erdos_problem_148.three_aux hz h3 h1 (by linarith)
        subst e1 e2 e3
        decide
    · rintro rfl
      refine ⟨by decide, by decide, ?_⟩
      norm_num
  unfold egyptianFractionCount
  rw [h, Set.ncard_singleton]
