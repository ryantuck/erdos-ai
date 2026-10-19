-- [AI - Claude Opus 5.5]: Erdős Problem 176 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Data.ZMod.Basic

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #176

*Source:* [erdosproblems.com/176](https://www.erdosproblems.com/176) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-02-20; page edited 28 December
2025). [Er65b] [Er73] [Er74b] [Er75b] [ErGr79] [Er80] [ErGr80, p.15]

Let $N(k,\ell)$ be the minimal $N$ such that for any $f:\{1,\ldots,N\}\to\{-1,1\}$ there must
exist a $k$-term arithmetic progression $P$ such that $\left|\sum_{n\in P}f(n)\right|\geq\ell$.
Find good upper bounds for $N(k,\ell)$. Is it true that for any $c>0$ there exists some $C>1$ such
that $N(k,ck)\leq C^k$? What about $N(k,2)\leq C^k$ or $N(k,\sqrt{k})\leq C^k$?

Remarks recorded on the page: when $\ell=k$ this is the van der Waerden number $W(k)$ (see [138]).
Spencer [Sp73] has proved that if $k=2^tm$ with $m$ odd then $N(k,1)=2^t(k-1)+1$. Erdős and Graham
write that 'no decent bound' is known even for $N(k,2)$. Erdős [Er63d] proved that, for every $c>0$,
$N(k,ck)>(1+\alpha_c)^k$ where $\alpha_c\to0$ as $c\to0$ and $\alpha_c\to\sqrt2-1$ as $c\to1$.

## Encoding notes

* The three yes/no questions are open; each is asserted in its "yes" direction. "Find good upper
  bounds" has no formal target.
* `discrepancyAPNumber k ℓ` is `sInf` of the admissible `N`. When `ℓ > k` no `N` is admissible (a
  sum of `k` signs has absolute value at most `k`), and the value is the junk `0`
  (`eq_zero_of_lt`, PROVED). So `176a` is trivially true for `c > 1`; its content is `0 < c ≤ 1`,
  where the set is nonempty by van der Waerden's theorem. The junk value only affects meaningless
  cases.
* Checks against Spencer's formula (PROVED in Lean): `N(k, 1) = k` for odd `k` (`spencer_odd`) and
  `N(2, 1) = 3` (`two_one`).

## References

From the site's `/latex/176` bibliography:
* [Er63d] Erdős, P., _On combinatorial questions connected with a theorem of Ramsey and van der
  Waerden_. Mat. Lapok (1963), 29–37.
* [Sp73] Spencer, J., _Problem 185_. Canad. Math. Bull. (1973), 185.

Erdős's sources, from the site's bibliographies of other problems:
* [Er65b] Erdős, P., _Some recent advances and current problems in number theory_. Lectures on
  Modern Mathematics, Vol. III (1965), 196–244. (Site `/latex/977`.)
* [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial
  theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973),
  117–138. (Site `/latex/783` and others.)
* [Er74b] Erdős, P., _Remarks on some problems in number theory_. Math. Balkanica (1974), 197–202.
  (Site `/latex/823`, `/latex/820`.)
* [Er75b] Erdős, P., _Problems and results in combinatorial number theory_. Journées Arithmétiques
  de Bordeaux (Conf., Univ. Bordeaux, Bordeaux, 1974) (1975), 295–310. (Site `/latex/656` and
  others.)
* [Er80] Erdős, P., _A survey of problems in combinatorial number theory_. Ann. Discrete Math.
  (1980), 89–115. (Site `/latex/425`.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/176.lean` (Opus 5.5 review, `opus-5-5-review/176.md`).
-/

/-- The arithmetic progression discrepancy number N(k, ℓ): the minimal N such
    that for every f : {1,...,N} → {-1,1}, there exists a k-term arithmetic
    progression a, a+d, ..., a+(k-1)d with d ≥ 1 and all terms in {1,...,N}
    such that |∑ᵢ f(a + id)| ≥ ℓ. -/
noncomputable def discrepancyAPNumber (k : ℕ) (ℓ : ℝ) : ℕ :=
  sInf { N : ℕ | ∀ f : ℕ → ℤ,
    (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
    ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
      ℓ ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| }

/--
Erdős Conjecture (Problem #176a) [Er65b, Er73, ErGr80]:
For any c > 0, there exists some C > 1 such that N(k, ck) ≤ Cᵏ. (Status: OPEN.)
-/
theorem erdos_problem_176a :
    ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (c * ↑k) : ℝ) ≤ C ^ k :=
  sorry

/--
Erdős Conjecture (Problem #176b) [Er65b, Er73, ErGr80]:
There exists some C > 1 such that N(k, 2) ≤ Cᵏ. (Status: OPEN.)
-/
theorem erdos_problem_176b :
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k 2 : ℝ) ≤ C ^ k :=
  sorry

/--
Erdős Conjecture (Problem #176c) [Er65b, Er73, ErGr80]:
There exists some C > 1 such that N(k, √k) ≤ Cᵏ. (Status: OPEN.)
-/
theorem erdos_problem_176c :
    ∃ C : ℝ, 1 < C ∧
    ∀ k : ℕ, (discrepancyAPNumber k (Real.sqrt ↑k) : ℝ) ≤ C ^ k :=
  sorry

/-- A sum of `k` values `±1` has absolute value at most `k` (PROVED in Lean). -/
theorem erdos_problem_176.abs_sum_le {k : ℕ} {g : ℕ → ℤ} (hg : ∀ i, g i = 1 ∨ g i = -1) :
    |(↑(∑ i ∈ range k, g i) : ℝ)| ≤ k := by
  have h : |∑ i ∈ range k, g i| ≤ ∑ i ∈ range k, |g i| := Finset.abs_sum_le_sum_abs _ _
  have h1 : ∑ i ∈ range k, |g i| = k := by
    rw [Finset.sum_congr rfl (fun i _ => show |g i| = 1 by rcases hg i with h | h <;> simp [h])]
    simp
  rw [h1] at h
  have : (|∑ i ∈ range k, g i| : ℤ) ≤ (k : ℤ) := h
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- For `ℓ > k` no `N` qualifies and `discrepancyAPNumber k ℓ` is the junk value `0` (PROVED in
Lean). This makes `176a` trivially true for `c > 1`. -/
theorem erdos_problem_176.eq_zero_of_lt {k : ℕ} {ℓ : ℝ} (h : (k : ℝ) < ℓ) : discrepancyAPNumber k ℓ = 0 := by
  unfold discrepancyAPNumber
  convert Nat.sInf_empty
  ext N
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hN
  obtain ⟨a, d, -, -, -, hℓ⟩ := hN (fun _ => 1) (fun _ _ _ => Or.inl rfl)
  have := erdos_problem_176.abs_sum_le (k := k) (g := fun i => (fun _ => (1 : ℤ)) (a + i * d)) (fun _ => Or.inl rfl)
  linarith

/-- Spencer's formula [Sp73] for odd `k` (`t = 0`): `N(k, 1) = k` (PROVED in Lean). A sum of an odd
number of signs is odd, hence nonzero, and a `k`-term progression in `{1, …, N}` needs `N ≥ k`. -/
theorem erdos_problem_176.spencer_odd {k : ℕ} (hk : k % 2 = 1) : discrepancyAPNumber k 1 = k := by
  have hmem : k ∈ { N : ℕ | ∀ f : ℕ → ℤ,
      (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
      ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
        (1 : ℝ) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| } := by
    intro f hf
    refine ⟨1, 1, Nat.one_pos, le_rfl, by omega, ?_⟩
    have hcast : ((∑ i ∈ range k, f (1 + i * 1) : ℤ) : ZMod 2) = 1 := by
      rw [Int.cast_sum]
      rw [Finset.sum_congr rfl (fun i hi => show ((f (1 + i * 1) : ℤ) : ZMod 2) = 1 by
        rcases hf (1 + i * 1) (by omega) (by rw [Finset.mem_range] at hi; omega) with h | h <;>
          rw [h] <;> push_cast <;> decide)]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [← ZMod.natCast_mod k 2, hk]
      simp
    have hne : (∑ i ∈ range k, f (1 + i * 1) : ℤ) ≠ 0 := by
      intro h0
      rw [h0] at hcast
      simp at hcast
    have h1 : (1 : ℤ) ≤ |∑ i ∈ range k, f (1 + i * 1)| := Int.one_le_abs hne
    rw [← Int.cast_abs]
    exact_mod_cast h1
  apply le_antisymm (Nat.sInf_le hmem)
  have hne : ({ N : ℕ | ∀ f : ℕ → ℤ,
      (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
      ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (k - 1) * d ≤ N ∧
        (1 : ℝ) ≤ |(↑(∑ i ∈ range k, f (a + i * d)) : ℝ)| }).Nonempty := ⟨k, hmem⟩
  obtain hS := Nat.sInf_mem hne
  obtain ⟨a, d, hd, ha, hlast, -⟩ := hS (fun _ => 1) (fun _ _ _ => Or.inl rfl)
  have : (k - 1) * 1 ≤ (k - 1) * d := Nat.mul_le_mul_left _ hd
  omega

/-- Spencer's formula [Sp73] for `k = 2` (`t = 1`, `m = 1`): `N(2, 1) = 3` (PROVED in Lean). -/
theorem erdos_problem_176.two_one : discrepancyAPNumber 2 1 = 3 := by
  have hmem : 3 ∈ { N : ℕ | ∀ f : ℕ → ℤ,
      (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
      ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (2 - 1) * d ≤ N ∧
        (1 : ℝ) ≤ |(↑(∑ i ∈ range 2, f (a + i * d)) : ℝ)| } := by
    intro f hf
    have key : ∀ a d : ℕ, 0 < d → 1 ≤ a → a + d ≤ 3 → f (a + d) = f a →
        ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (2 - 1) * d ≤ 3 ∧
          (1 : ℝ) ≤ |(↑(∑ i ∈ range 2, f (a + i * d)) : ℝ)| := by
      intro a d hd ha had heq
      refine ⟨a, d, hd, ha, by omega, ?_⟩
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, add_zero,
        one_mul, heq]
      rcases hf a ha (by omega) with h | h <;> simp [h]
    by_cases e12 : f (1 + 1) = f 1
    · exact key 1 1 one_pos le_rfl (by norm_num) e12
    by_cases e23 : f (2 + 1) = f 2
    · exact key 2 1 one_pos (by norm_num) (by norm_num) e23
    · apply key 1 2 (by norm_num) le_rfl (by norm_num)
      have h1 := hf 1 le_rfl (by norm_num)
      have h2 := hf 2 (by norm_num) (by norm_num)
      have h3 := hf 3 (by norm_num) le_rfl
      norm_num at e12 e23 ⊢
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> simp_all
  apply le_antisymm (Nat.sInf_le hmem)
  have hne : ({ N : ℕ | ∀ f : ℕ → ℤ,
      (∀ n, 1 ≤ n → n ≤ N → (f n = 1 ∨ f n = -1)) →
      ∃ a d : ℕ, 0 < d ∧ 1 ≤ a ∧ a + (2 - 1) * d ≤ N ∧
        (1 : ℝ) ≤ |(↑(∑ i ∈ range 2, f (a + i * d)) : ℝ)| }).Nonempty := ⟨3, hmem⟩
  obtain hS := Nat.sInf_mem hne
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, d, hd, ha, hlast, hsum⟩ :=
    hS (fun n => if n % 2 = 1 then 1 else -1) (fun n _ _ => by by_cases h : n % 2 = 1 <;> simp [h])
  have ha1 : a = 1 := by omega
  have hd1 : d = 1 := by omega
  subst ha1 hd1
  norm_num [Finset.sum_range_succ] at hsum

/-- Spencer [Sp73] (SOLVED; not proved here): if `k = 2^t m` with `m` odd then
`N(k, 1) = 2^t (k - 1) + 1`. -/
theorem erdos_problem_176.variants.spencer :
    ∀ t m : ℕ, m % 2 = 1 →
      discrepancyAPNumber (2 ^ t * m) 1 = 2 ^ t * (2 ^ t * m - 1) + 1 :=
  sorry

/-- Erdős [Er63d] (SOLVED; not proved here): for every `0 < c ≤ 1` there is `α > 0` with
`N(k, ck) > (1 + α)^k` for all large `k`. (For `c > 1` the value is the junk `0`.) -/
theorem erdos_problem_176.variants.erdos_lower :
    ∀ c : ℝ, 0 < c → c ≤ 1 → ∃ α : ℝ, 0 < α ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (1 + α) ^ k < (discrepancyAPNumber k (c * ↑k) : ℝ) :=
  sorry

end
