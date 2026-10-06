-- [AI - Claude Sonnet 5.5]: Erdős Problem 142 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset Filter

/-!
# Erdős Problem #142: An Asymptotic Formula for $r_k(N)$

*Source:* [erdosproblems.com/142](https://www.erdosproblems.com/142) (banner **OPEN**, prize
**\$10000**: "This is open, and cannot be resolved with a finite computation."; page last edited
23 January 2026; captured 2026-03-05 as the tidied problem box). [Er80] [Er81, p.4] [Er97c] [Va99, 1.27]

Let $r_k(N)$ be the largest possible size of a subset of $\{1,\ldots,N\}$ that does not contain any
non-trivial $k$-term arithmetic progression. Prove an asymptotic formula for $r_k(N)$.

Remarks recorded on the page:
* Erdős remarked this is "probably unattackable at present". In [Er97c] Erdős offered \$1000, but given
  that he elsewhere offered \$5000 just for (essentially) showing that $r_k(N)=o_k(N/\log N)$ (see [3]),
  that value seems odd. In [Er81] he offers \$10000, stating it is "probably enormously difficult".
* The best known upper bounds for $r_k(N)$ are due to Kelley and Meka [KeMe23] for $k=3$, Green and Tao
  [GrTa17] for $k=4$, and Leng, Sah, and Sawhney [LSS24] for $k\geq 5$. An asymptotic formula is still
  far out of reach, even for $k=3$.
* In [Va99] he asks (much more reasonably) for the order of magnitude of $r_k(N)$.
* See also [3] and [139].

Tags: additive combinatorics, arithmetic progressions. OEIS: A003002, A003003, A003004, A003005. 0 comments
at capture.

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31 with prize \$10000.
Upstream has `erdos_142`, category `research open`, stated as `r k N ~ answer(sorry)`.

**What the first pass got wrong, and what this file does.** The first pass states
`∃ f : ℕ → ℝ, (∀ᶠ N, 0 < f N) ∧ r_k(N) / f N → 1`, with no restriction on `f`. That is **trivially true**:
take `f N = r_k(N)`, which is positive for `N ≥ 1`, and the ratio is `1`. `variants.first_pass_trivial`
proves it in Lean. So the first pass's theorem says nothing about the problem, and a proof of it would not
settle Problem 142. An "asymptotic formula" is a *closed form*, and the page does not say which closed
forms count. v2 makes that explicit:
* `IsExpLog f` says that `f : ℝ → ℝ` is built from constants and the identity by sums, products,
  reciprocals, `exp` and `log`. It contains `x ^ a`, `(log x) ^ b`, `x * exp (-c * (log x) ^ δ)` and the like,
  and none of the arithmetic fluctuations of `r_k`.
* The main theorem asks for an `IsExpLog` function `f` with `r_k(N) / f(N) → 1`.
This class is an editorial choice. It is what makes the statement mean what the problem asks, and a
different closed-form class would give a different, comparable statement.

**Encoding.**
* `APFree k S` and `rk k N` are the first pass's definitions. `rk k N` is the `sSup` of the sizes of the
  `k`-progression-free subsets of `{0, …, N-1}`. The set of sizes contains `0` and is bounded by `N`, so
  `sSup` is its maximum. The page uses `{1, …, N}`, and a shift by one changes nothing.
* The main theorem has `k ≥ 3`, as the input does. For `k ≤ 2` the function `r_k` is `0` or at most `1`.
* `variants.rk_three_nine` proves `r_3(9) = 5` in Lean, the classical value, with `apFree_iff_bounded` as the
  finite-check lemma. It shows that `rk` is the true maximum on a non-trivial instance.
* `variants.three` is the page's remark that the case `k = 3` is already out of reach.
* `variants.order_of_magnitude` is the question of [Va99], with the same closed-form class, and
  `variants.order_of_magnitude_of_main` shows that an asymptotic formula gives it.
* `variants.o_over_log` is the statement for which the page records Erdős's offer of \$5000
  ("essentially", see [3]). It is OPEN as a statement about every `k ≥ 3`.
* The best known upper bounds are named on the page without formulas and are not formalized.

## References

* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math. (1980),
  89–115.
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42. The page cites p. 4.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul Erdős and
  his mathematics", Budapest, July 1999. The page cites problem 1.27.
* [KeMe23] Kelley, Z. and Meka, R., _Strong bounds for 3-progressions_. arXiv:2302.05537 (2023).
* [LSS24] Leng, J., Sah, A. and Sawhney, M. **DEFERRED:** no title or venue was recovered.
* [GrTa17] cited on the page. **DEFERRED:** no bibliographic data was recovered.
* [3], [139] The page's cross-references to Problems 3 and 139.

(Provenance: [Er80], [Er81], [Er97c], [Va99] and [KeMe23] are from the bibliographies of the `/latex`
pages of other problems. **DEFERRED:** no `/latex/142` fetch exists in the logs, so the entries were not
checked against the page's own bibliography.)
-/

/--
A Finset S of natural numbers is free of non-trivial k-term arithmetic
progressions: there do not exist a, d with d ≥ 1 such that
{a, a+d, …, a+(k-1)d} ⊆ S.
-/
def APFree (k : ℕ) (S : Finset ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → ∃ i : ℕ, i < k ∧ a + i * d ∉ S

/--
r_k(N) is the largest size of a subset of {0, …, N-1} with no non-trivial
k-term arithmetic progression.
-/
noncomputable def rk (k N : ℕ) : ℕ :=
  sSup ((fun S => S.card) '' {S : Finset ℕ | S ⊆ Finset.range N ∧ APFree k S})

/--
The closed forms: functions built from constants and the identity by sums, products, reciprocals,
`exp` and `log`. An "asymptotic formula" is read as an asymptotic equivalence with such a function.
-/
inductive IsExpLog : (ℝ → ℝ) → Prop
  | const (c : ℝ) : IsExpLog (fun _ => c)
  | id : IsExpLog (fun x => x)
  | add {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x + g x)
  | mul {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x * g x)
  | inv {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => (f x)⁻¹)
  | exp {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.exp (f x))
  | log {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.log (f x))

/--
Erdős Problem #142 [Er80, Er81, Er97c, Va99] — OPEN (\$10000):

Let r_k(N) be the largest possible size of a subset of {1,…,N} that does not
contain any non-trivial k-term arithmetic progression. Prove an asymptotic formula for r_k(N).

More precisely: for each k ≥ 3, there exists a closed-form function f (built from constants and the
identity by sums, products, reciprocals, exp and log) such that r_k(N) / f(N) → 1 as N → ∞.

Erdős called this 'probably unattackable at present' and offered $10000 for a
proof [Er81]. An asymptotic formula is still far out of reach, even for k = 3.
-/
theorem erdos_problem_142 (k : ℕ) (hk : 3 ≤ k) :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ (∀ᶠ N : ℕ in atTop, 0 < f N) ∧
      Tendsto (fun N : ℕ => (rk k N : ℝ) / f N) atTop (nhds 1) :=
  sorry

/-- The size bound: every `k`-progression-free subset of `{0, …, N-1}` has at most `rk k N` elements
(PROVED in Lean). -/
theorem erdos_problem_142.card_le_rk {k N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N)
    (hf : APFree k S) : S.card ≤ rk k N := by
  unfold rk
  apply le_csSup
  · refine ⟨N, ?_⟩
    rintro m ⟨T, ⟨hT, _⟩, rfl⟩
    simpa using Finset.card_le_card hT
  · exact ⟨S, ⟨hS, hf⟩, rfl⟩

/-- For `k ≥ 2` and `N ≥ 1`, `rk k N ≥ 1`, from the progression-free set `{0}` (PROVED in Lean). -/
theorem erdos_problem_142.one_le_rk {k N : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) : 1 ≤ rk k N := by
  have hS : ({0} : Finset ℕ) ⊆ Finset.range N := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    subst hx
    simpa using hN
  have hf : APFree k ({0} : Finset ℕ) := by
    intro a d hd
    refine ⟨1, by omega, ?_⟩
    simp only [Finset.mem_singleton]
    omega
  simpa using erdos_problem_142.card_le_rk hS hf

/-- For `k ≥ 2` and `S ⊆ {0, …, N-1}`, `APFree k S` only needs the starting points `a < N` and the
differences `d < N` (PROVED in Lean). A progression with `a ≥ N` or `d ≥ N` already leaves the range, at
its first or its second term. This turns `APFree` into a finite check. -/
theorem erdos_problem_142.apFree_iff_bounded {k N : ℕ} (hk : 2 ≤ k) {S : Finset ℕ}
    (hS : S ⊆ Finset.range N) :
    APFree k S ↔ ∀ a < N, ∀ d < N, 0 < d → ∃ i < k, a + i * d ∉ S := by
  constructor
  · intro h a _ d _ hd
    exact h a d hd
  · intro h a d hd
    by_cases ha : a < N
    · by_cases hd' : d < N
      · exact h a ha d hd' hd
      · refine ⟨1, by omega, ?_⟩
        intro hmem
        have := Finset.mem_range.mp (hS hmem)
        omega
    · refine ⟨0, by omega, ?_⟩
      intro hmem
      have := Finset.mem_range.mp (hS hmem)
      omega

/--
The classical value `r_3(9) = 5` (PROVED in Lean), attained by `{1, 2, 4, 8, 9}`, here shifted to
`{0, 1, 3, 7, 8}`. It checks that `rk` is the true maximum on a non-trivial instance: the upper bound is a
finite check over the `2 ^ 9` subsets of `{0, …, 8}`.
-/
theorem erdos_problem_142.variants.rk_three_nine : rk 3 9 = 5 := by
  apply le_antisymm
  · unfold rk
    apply csSup_le
    · exact ⟨0, ∅, ⟨Finset.empty_subset _, fun a d _ => ⟨0, by omega, by simp⟩⟩, rfl⟩
    · rintro m ⟨S, ⟨hS, hf⟩, rfl⟩
      have key : ∀ T ∈ (Finset.range 9).powerset,
          (∀ a < 9, ∀ d < 9, 0 < d → ∃ i < 3, a + i * d ∉ T) → T.card ≤ 5 := by
        decide +kernel
      exact key S (Finset.mem_powerset.mpr hS)
        ((erdos_problem_142.apFree_iff_bounded (by norm_num) hS).mp hf)
  · have hS : ({0, 1, 3, 7, 8} : Finset ℕ) ⊆ Finset.range 9 := by decide
    have hf : APFree 3 ({0, 1, 3, 7, 8} : Finset ℕ) :=
      (erdos_problem_142.apFree_iff_bounded (by norm_num) hS).mpr (by decide +kernel)
    simpa using erdos_problem_142.card_le_rk hS hf

/--
The first pass's statement is trivially true (PROVED in Lean): take `f N = r_k(N)`, which is positive for
`N ≥ 1`. It carries no information about an asymptotic formula, which is why the main theorem restricts
`f` to closed forms.
-/
theorem erdos_problem_142.variants.first_pass_trivial (k : ℕ) (hk : 3 ≤ k) :
    ∃ f : ℕ → ℝ, (∀ᶠ N in atTop, 0 < f N) ∧
      Tendsto (fun N => (rk k N : ℝ) / f N) atTop (nhds 1) := by
  refine ⟨fun N => (rk k N : ℝ), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact_mod_cast erdos_problem_142.one_le_rk (by omega) hN
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have : (0 : ℝ) < (rk k N : ℝ) := by
      exact_mod_cast erdos_problem_142.one_le_rk (by omega) hN
    exact (div_self this.ne').symm

/--
The case `k = 3` of the main theorem (OPEN): the page remarks that an asymptotic formula is out of reach
"even for `k = 3`". It is stated as an instance of the main theorem, so it depends on that theorem's `sorry`.
-/
theorem erdos_problem_142.variants.three :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ (∀ᶠ N : ℕ in atTop, 0 < f N) ∧
      Tendsto (fun N : ℕ => (rk 3 N : ℝ) / f N) atTop (nhds 1) :=
  erdos_problem_142 3 le_rfl

/--
The question of [Va99] (OPEN), with the same closed-form class: is `r_k(N)` of the order of a closed form?
-/
theorem erdos_problem_142.variants.order_of_magnitude (k : ℕ) (hk : 3 ≤ k) :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, c * f N ≤ (rk k N : ℝ) ∧ (rk k N : ℝ) ≤ C * f N :=
  sorry

/--
An asymptotic formula gives the order of magnitude (PROVED in Lean): if `r_k(N) / f(N) → 1` with `f`
positive, then `f / 2 ≤ r_k ≤ 3 f / 2` for large `N`.
-/
theorem erdos_problem_142.variants.order_of_magnitude_of_main (k : ℕ)
    (hmain : ∃ f : ℝ → ℝ, IsExpLog f ∧ (∀ᶠ N : ℕ in atTop, 0 < f N) ∧
      Tendsto (fun N : ℕ => (rk k N : ℝ) / f N) atTop (nhds 1)) :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ N : ℕ in atTop, c * f N ≤ (rk k N : ℝ) ∧ (rk k N : ℝ) ≤ C * f N := by
  obtain ⟨f, hf, hpos, ht⟩ := hmain
  refine ⟨f, hf, 1 / 2, 3 / 2, by norm_num, by norm_num, ?_⟩
  have h1 : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) < (rk k N : ℝ) / f N :=
    ht.eventually (lt_mem_nhds (by norm_num))
  have h2 : ∀ᶠ N : ℕ in atTop, (rk k N : ℝ) / f N < 3 / 2 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hpos, h1, h2] with N hp h1 h2
  rw [lt_div_iff₀ hp] at h1
  rw [div_lt_iff₀ hp] at h2
  constructor <;> linarith

/--
The statement behind Erdős's offer of \$5000 (see [3]), "essentially" as the page words it (OPEN as a
statement about every `k ≥ 3`): `r_k(N) = o_k(N / log N)`.
-/
theorem erdos_problem_142.variants.o_over_log :
    ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (rk k N : ℝ) ≤ ε * (N : ℝ) / Real.log (N : ℝ) :=
  sorry
