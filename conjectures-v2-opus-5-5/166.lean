-- [AI - Claude Opus 5.5]: Erdős Problem 166 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #166

*Source:* [erdosproblems.com/166](https://www.erdosproblems.com/166) (status **PROVED**: "This has
been solved in the affirmative."; prize \$250; captured 2026-02-20; page edited 23 January 2026;
OEIS A059442). [Er90b] [Er91] [Er93, p.339] [Er97c] [Va99, 3.51]

Prove that $R(4,k)\gg\frac{k^3}{(\log k)^{O(1)}}$.

Remarks recorded on the page: Spencer [Sp77] proved $R(4,k)\gg(k\log k)^{5/2}$. Ajtai, Komlós and
Szemerédi [AKS80] proved $R(4,k)\ll\frac{k^3}{(\log k)^2}$. This is true, and was proved by Mattheus
and Verstraete [MaVe23], who showed that $R(4,k)\gg\frac{k^3}{(\log k)^4}$. This problem is #5 in
Ramsey Theory in the graphs problem collection. See also [986] for the general case.

After the capture, the mirror (`b916d95`) records `formalized: yes` (2026-09-09), and upstream
`formal-conjectures` (`df3f12d`) links a Lean proof of its version of the statement. Neither proof
was examined here.

## Encoding notes

* "$\gg k^3/(\log k)^{O(1)}$" is encoded as: there are `C > 0` and an exponent `α : ℕ` with
  `C · k³ / (log k)^α ≤ R(4,k)` for all large `k`. A natural exponent loses nothing: the version
  with a real exponent is equivalent (`variants.main_iff_rpow`, PROVED in Lean), because
  `log k ≥ 1` for `k ≥ 4` (`one_le_log`), so raising the exponent only weakens the bound.
* The statement is not trivial for any fixed `α`: by [AKS80], any admissible exponent is at least
  `2` (`variants.exponent_ge_two`, PROVED in Lean from the [AKS80] bound), and [Sp77]'s
  $(k\log k)^{5/2}$ is too small for every `α`.
* `ramseyR4 k` is the least `N` such that every graph on `Fin N` has a `4`-clique or an independent
  `k`-set. The set is nonempty by Ramsey's theorem (not formalized here). The definition gives
  `ramseyR4 0 = 0` and `ramseyR4 1 = 1` (PROVED).
* The small `k` where `Real.log k ≤ 1` are excluded by the threshold `N₀`.

## References

From the site's `/latex/166` bibliography:
* [Sp77] Spencer, J., _Asymptotic lower bounds for Ramsey functions_. Discrete Math. (1977), 69–76.
* [AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_. J. Combin. Theory
  Ser. A (1980), 354–360.
* [MaVe23] Mattheus, S. and Verstraete, J., _The asymptotics of $r(4,t)$_. arXiv:2306.04007 (2023).
  (Published in Ann. of Math. (2024) according to upstream; the page range is not checked here.)

Erdős's sources, from the site's bibliographies of other problems:
* [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and differences_.
  Mathematics of Ramsey theory (1990), 12–28. (Site `/latex/161`.)
* [Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number theory_.
  Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991), 397–406. (Site
  `/latex/86`.)
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_. Quaestiones
  Math. (1993), 333–350. (Site `/latex/181`.)
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul Erdős, I
  (1997), 47–67. (Site `/latex/94`.)
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference "Paul
  Erdős and his mathematics", Budapest, July 1999. (Site `/latex/59` and others.)

*Provenance:* second pass of `conjectures/166.lean` (Opus 5.5 review, `opus-5-5-review/166.md`).
-/

open SimpleGraph Real

noncomputable section

/-- The Ramsey number R(4,k): the minimum N such that every simple graph
    on N vertices contains either a 4-clique or an independent set of
    size k (a k-clique in the complement). -/
noncomputable def ramseyR4 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Conjecture (Problem #166) [Er90b, Er91, Er93, Er97c]:

There exist constants C > 0 and α : ℕ such that for all sufficiently large k,
  R(4,k) ≥ C · k³ / (log k)^α.

In asymptotic notation: R(4,k) ≫ k³/(log k)^{O(1)}.

This was proved by Mattheus and Verstraete [MaVe23], who showed
  R(4,k) ≫ k³/(log k)⁴. (Status: PROVED, \$250.)
-/
theorem erdos_problem_166 :
    ∃ C : ℝ, 0 < C ∧
    ∃ α : ℕ,
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ) :=
  sorry

/-- `R(4,0) = 0` with this definition: the empty vertex set is a `0`-clique of every complement
(PROVED in Lean). -/
theorem erdos_problem_166.ramseyR4_zero : ramseyR4 0 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (fun _ => Or.inr not_cliqueFree_zero))

/-- `R(4,1) = 1`: one vertex is an independent `1`-set, and the graph on no vertices has neither a
`4`-clique nor a vertex (PROVED in Lean). -/
theorem erdos_problem_166.ramseyR4_one : ramseyR4 1 = 1 := by
  have h1 : (1 : ℕ) ∈ {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree 1} := by
    intro G
    right
    rw [SimpleGraph.cliqueFree_one]
    exact not_isEmpty_of_nonempty (Fin 1)
  have h0 : (0 : ℕ) ∉ {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 4 ∨ ¬Gᶜ.CliqueFree 1} := by
    intro h
    rcases h ⊥ with h4 | h1'
    · exact h4 (SimpleGraph.cliqueFree_of_card_lt (by simp))
    · exact h1' (by rw [SimpleGraph.cliqueFree_one]; infer_instance)
  apply le_antisymm (Nat.sInf_le h1)
  rcases Nat.eq_zero_or_pos (ramseyR4 1) with h | h
  · exfalso
    apply h0
    unfold ramseyR4 at h
    rw [← h]
    exact Nat.sInf_mem ⟨1, h1⟩
  · exact h

/-- `1 ≤ log k` for `k ≥ 4` (PROVED in Lean; `exp 1 ≤ 4` from `exp (-1/2) ≥ 1/2`); used to compare
powers of `log k`. -/
theorem erdos_problem_166.one_le_log {k : ℕ} (hk : 4 ≤ k) : 1 ≤ Real.log (k : ℝ) := by
  have hk' : (4 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2)) := by
    have := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  have h2 : Real.exp (1 / 2) * Real.exp (-(1 / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (1 / 2) ≤ 2 := by
    have hpos := Real.exp_pos (1 / 2 : ℝ)
    nlinarith
  have h4 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]; norm_num
  have hpos := Real.exp_pos (1 / 2 : ℝ)
  nlinarith

/-- The exponent may be taken real: the main theorem is equivalent to the same bound with
`(log k) ^ c` for a real `c` (PROVED in Lean). -/
theorem erdos_problem_166.variants.main_iff_rpow :
    (∃ C : ℝ, 0 < C ∧
      ∃ α : ℕ,
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ)) ↔
    (∃ C : ℝ, 0 < C ∧
      ∃ c : ℝ,
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ c) ≤ (ramseyR4 k : ℝ)) := by
  constructor
  · rintro ⟨C, hC, α, N₀, h⟩
    refine ⟨C, hC, α, N₀, fun k hk => ?_⟩
    rw [Real.rpow_natCast]
    exact h k hk
  · rintro ⟨C, hC, c, N₀, h⟩
    refine ⟨C, hC, ⌈c⌉₊, max N₀ 4, fun k hk => ?_⟩
    have hL := erdos_problem_166.one_le_log (le_trans (le_max_right _ _) hk)
    have hpow : Real.log (k : ℝ) ^ c ≤ Real.log (k : ℝ) ^ ⌈c⌉₊ := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hL (Nat.le_ceil c)
    have hdiv : (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ ⌈c⌉₊ ≤ (k : ℝ) ^ 3 / Real.log (k : ℝ) ^ c :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos (by linarith) c) hpow
    exact le_trans (mul_le_mul_of_nonneg_left hdiv hC.le) (h k (le_trans (le_max_left _ _) hk))

/-- Mattheus and Verstraete [MaVe23] (SOLVED; not proved here): $R(4,k)\gg k^3/(\log k)^4$. -/
theorem erdos_problem_166.variants.mattheus_verstraete :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ 4) ≤ (ramseyR4 k : ℝ) :=
  sorry

/-- [MaVe23]'s bound implies the main theorem, with `α = 4` (PROVED in Lean). -/
theorem erdos_problem_166.variants.main_of_mattheus_verstraete
    (h : ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ 4) ≤ (ramseyR4 k : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
    ∃ α : ℕ,
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ) := by
  obtain ⟨C, hC, N₀, hN⟩ := h
  exact ⟨C, hC, 4, N₀, hN⟩

/-- Ajtai, Komlós and Szemerédi [AKS80] (SOLVED; not proved here): $R(4,k)\ll k^3/(\log k)^2$. -/
theorem erdos_problem_166.variants.aks :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (ramseyR4 k : ℝ) ≤ C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ 2) :=
  sorry

/-- Spencer [Sp77] (SOLVED; not proved here): $R(4,k)\gg(k\log k)^{5/2}$. -/
theorem erdos_problem_166.variants.spencer :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) * Real.log (k : ℝ)) ^ ((5 : ℝ) / 2) ≤ (ramseyR4 k : ℝ) :=
  sorry

/-- Given the [AKS80] upper bound, an exponent `α` that works in the main theorem is at least `2`
(PROVED in Lean from the bound). So the main theorem is not trivial for any `α`. -/
theorem erdos_problem_166.variants.exponent_ge_two {C : ℝ} {α : ℕ} (hC : 0 < C)
    (h : ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      C * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ α) ≤ (ramseyR4 k : ℝ))
    (hup : ∃ C' : ℝ, 0 < C' ∧
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        (ramseyR4 k : ℝ) ≤ C' * ((k : ℝ) ^ 3 / (Real.log (k : ℝ)) ^ 2)) :
    2 ≤ α := by
  obtain ⟨N₁, h₁⟩ := h
  obtain ⟨C', hC', N₂, h₂⟩ := hup
  by_contra hα
  push_neg at hα
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (C' / C + 1))
  have hk1 : N₁ ≤ max (max N₁ N₂) (max n 4) := le_trans (le_max_left _ _) (le_max_left _ _)
  have hk2 : N₂ ≤ max (max N₁ N₂) (max n 4) := le_trans (le_max_right _ _) (le_max_left _ _)
  have hkn : n ≤ max (max N₁ N₂) (max n 4) := le_trans (le_max_left _ _) (le_max_right _ _)
  have hk3 : 4 ≤ max (max N₁ N₂) (max n 4) := le_trans (le_max_right _ _) (le_max_right _ _)
  set k := max (max N₁ N₂) (max n 4)
  have hkpos : (0 : ℝ) < k := by
    have : (4 : ℝ) ≤ k := by exact_mod_cast hk3
    linarith
  have hL1 := erdos_problem_166.one_le_log hk3
  have hLpos : 0 < Real.log (k : ℝ) := by linarith
  have hLbig : C' / C + 1 < Real.log (k : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hkpos]
    have : (n : ℝ) ≤ k := by exact_mod_cast hkn
    linarith
  have hLα : Real.log (k : ℝ) ^ α ≤ Real.log (k : ℝ) := by
    calc Real.log (k : ℝ) ^ α ≤ Real.log (k : ℝ) ^ 1 := pow_le_pow_right₀ hL1 (by omega)
      _ = Real.log (k : ℝ) := pow_one _
  have hX : 0 < (k : ℝ) ^ 3 / Real.log (k : ℝ) := by positivity
  have h3 : C * ((k : ℝ) ^ 3 / Real.log (k : ℝ)) ≤
      C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ) / Real.log (k : ℝ)) := by
    calc C * ((k : ℝ) ^ 3 / Real.log (k : ℝ))
        ≤ C * ((k : ℝ) ^ 3 / Real.log (k : ℝ) ^ α) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hLα) hC.le
      _ ≤ C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ) ^ 2) := le_trans (h₁ k hk1) (h₂ k hk2)
      _ = C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ) / Real.log (k : ℝ)) := by
          rw [div_div, sq]
  have h4 : C * Real.log (k : ℝ) * ((k : ℝ) ^ 3 / Real.log (k : ℝ)) ≤
      C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ)) := by
    have := mul_le_mul_of_nonneg_right h3 hLpos.le
    calc C * Real.log (k : ℝ) * ((k : ℝ) ^ 3 / Real.log (k : ℝ))
        = C * ((k : ℝ) ^ 3 / Real.log (k : ℝ)) * Real.log (k : ℝ) := by ring
      _ ≤ C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ) / Real.log (k : ℝ)) * Real.log (k : ℝ) := this
      _ = C' * ((k : ℝ) ^ 3 / Real.log (k : ℝ)) := by field_simp
  have h5 : C * Real.log (k : ℝ) ≤ C' := le_of_mul_le_mul_right h4 hX
  have h6 : C * (C' / C + 1) = C' + C := by field_simp
  have h7 : C * (C' / C + 1) < C * Real.log (k : ℝ) := mul_lt_mul_of_pos_left hLbig hC
  linarith

end
