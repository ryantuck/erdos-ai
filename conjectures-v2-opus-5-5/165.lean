-- [AI - Claude Opus 5.5]: Erdős Problem 165 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem #165

*Source:* [erdosproblems.com/165](https://www.erdosproblems.com/165) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; prize \$250; captured 2026-02-20; page
edited 28 December 2025; OEIS A000791). [Er61] [Er71] [Er90b] [Er93, p.339] [Er97c]

Give an asymptotic formula for $R(3,k)$.

Remarks recorded on the page:
* There is a constant $c>0$ with $(c+o(1))\frac{k^2}{\log k}\le R(3,k)\le(1+o(1))\frac{k^2}{\log k}$
  for large $k$. The lower bound is due to Kim [Ki95]; the upper bound to Shearer [Sh83], improving
  Ajtai, Komlós and Szemerédi [AKS80].
* Kim's proof gave $c\ge1/162$. $c\ge1/4$ was proved independently by Bohman and Keevash [BoKe21] and
  by Fiz Pontiveros, Griffiths and Morris [PGM20], who conjectured that this is the truth. Campos,
  Jenssen, Michelen and Sahasrabudhe [CJMS25] improved this to $c\ge1/3$, and Hefty, Horn, King and
  Pfender [HHKP25] to $c\ge1/2$. Both papers conjecture $c=1/2$.
* See also [544], and [986] for the general case; [1013] for a related function.

## Encoding notes

* "Give an asymptotic formula" is a value request. Since the order $k^2/\log k$ is known, the input
  reads it as the existence of $c>0$ with $R(3,k)\sim c\,k^2/\log k$, i.e. convergence of
  $R(3,k)\log k/k^2$; this is the open content. The value $c=1/2$ that the recent papers conjecture
  is `variants.half`, and it implies the main theorem (`variants.main_of_half`, PROVED). With the
  known bounds, any such $c$ lies in $[1/2,1]$ (`variants.constant_mem`, PROVED from them).
* `ramseyR3 k` is the least `N` such that every graph on `Fin N` has a triangle or an independent
  `k`-set (a `k`-clique in the complement). The set is nonempty by Ramsey's theorem (not formalized
  here). The definition gives `ramseyR3 0 = 0` and `ramseyR3 1 = 1` (PROVED); an exhaustive search
  in the review gives $R(3,2),R(3,3),R(3,4)=3,6,9$, as in A000791.
* "$\sim$" is encoded as $(c\pm\varepsilon)\,k^2/\log k$ bounds for large $k$; `Real.log` is the
  natural logarithm, which fixes the meaning of the constant.

## References

From the site's `/latex/165` bibliography:
* [AKS80] Ajtai, M., Komlós, J. and Szemerédi, E., _A note on Ramsey numbers_. J. Combin. Theory
  Ser. A (1980), 354–360.
* [Sh83] Shearer, J., _A note on the independence number of triangle-free graphs_. Discrete Math.
  (1983), 83–87.
* [Ki95] Kim, J. H., _The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$_. Random
  Structures Algorithms (1995), 173–207.
* [PGM20] Fiz Pontiveros, G., Griffiths, S. and Morris, R., _The triangle-free process and the
  Ramsey number $R(3,k)$_. Mem. Amer. Math. Soc. (2020), v+125.
* [BoKe21] Bohman, T. and Keevash, P., _Dynamic concentration of the triangle-free process_. Random
  Structures Algorithms (2021), 221–293.
* [CJMS25] Campos, M., Jenssen, M., Michelen, M. and Sahasrabudhe, J., _A new lower bound for the
  Ramsey numbers $R(3,k)$_. arXiv:2505.13371 (2025).
* [HHKP25] Hefty, Z., Horn, P., King, D. and Pfender, F., _Improving $R(3,k)$ in just two bites_.
  arXiv:2510.19718 (2025).

Erdős's sources, from the site's bibliographies of other problems:
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254. (Site `/latex/511`.)
* [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109. (Site
  `/latex/1022`.)
* [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and differences_.
  Mathematics of Ramsey theory (1990), 12–28. (Site `/latex/161`.)
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_. Quaestiones
  Math. (1993), 333–350. (Site `/latex/181`.)
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul Erdős, I
  (1997), 47–67. (Site `/latex/94`.)

*Provenance:* second pass of `conjectures/165.lean` (Opus 5.5 review, `opus-5-5-review/165.md`).
-/

open SimpleGraph Real

noncomputable section

/-- The Ramsey number R(3,k): the minimum N such that every simple graph
    on N vertices contains either a triangle (3-clique) or an independent
    set of size k (a k-clique in the complement). -/
noncomputable def ramseyR3 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Conjecture (Problem #165) [Er61, Er71, Er90b, Er93, Er97c]:

There exists a constant c > 0 such that R(3,k) ~ c · k²/log k, i.e.,
for all ε > 0 and all sufficiently large k:
  (c - ε) · k²/log k ≤ R(3,k) ≤ (c + ε) · k²/log k.

The conjectured value is c = 1/2. (Status: OPEN, \$250.)
-/
theorem erdos_problem_165 :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (c - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (c + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  sorry

/-- `R(3,0) = 0` with this definition: the empty vertex set is a `0`-clique of every complement
(PROVED in Lean). -/
theorem erdos_problem_165.ramseyR3_zero : ramseyR3 0 = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (fun _ => Or.inr not_cliqueFree_zero))

/-- `R(3,1) = 1`: one vertex is an independent `1`-set, and the empty graph on no vertices has
neither a triangle nor a vertex (PROVED in Lean). -/
theorem erdos_problem_165.ramseyR3_one : ramseyR3 1 = 1 := by
  have h1 : (1 : ℕ) ∈ {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree 1} := by
    intro G
    right
    rw [SimpleGraph.cliqueFree_one]
    exact not_isEmpty_of_nonempty (Fin 1)
  have h0 : (0 : ℕ) ∉ {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree 1} := by
    intro h
    rcases h ⊥ with h3 | h1'
    · exact h3 (SimpleGraph.cliqueFree_of_card_lt (by simp))
    · exact h1' (by rw [SimpleGraph.cliqueFree_one]; infer_instance)
  apply le_antisymm (Nat.sInf_le h1)
  rcases Nat.eq_zero_or_pos (ramseyR3 1) with h | h
  · exfalso
    apply h0
    unfold ramseyR3 at h
    rw [← h]
    exact Nat.sInf_mem ⟨1, h1⟩
  · exact h

/-- The value conjectured by [CJMS25] and [HHKP25] (OPEN): $R(3,k)\sim\frac12\,k^2/\log k$. -/
theorem erdos_problem_165.variants.half :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (1 / 2 - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (1 / 2 + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  sorry

/-- The conjectured value implies the main theorem, with `c = 1/2` (PROVED in Lean). -/
theorem erdos_problem_165.variants.main_of_half
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        (1 / 2 - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
        (ramseyR3 k : ℝ) ≤ (1 / 2 + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (c - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
      (ramseyR3 k : ℝ) ≤ (c + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  ⟨1 / 2, by norm_num, h⟩

/-- Shearer's upper bound [Sh83] (SOLVED; not proved here): $R(3,k)\le(1+o(1))k^2/\log k$. -/
theorem erdos_problem_165.variants.shearer :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (ramseyR3 k : ℝ) ≤ (1 + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) :=
  sorry

/-- The lower bound of Hefty, Horn, King and Pfender [HHKP25] (SOLVED per the page, a 2025 preprint;
not proved here): $R(3,k)\ge(1/2-o(1))k^2/\log k$. Kim [Ki95] proved the order of magnitude. -/
theorem erdos_problem_165.variants.hhkp :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
      (1 / 2 - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) :=
  sorry

/-- With the known bounds, a constant `c` as in the main theorem lies in `[1/2, 1]` (PROVED in Lean
from the three statements). -/
theorem erdos_problem_165.variants.constant_mem {c : ℝ}
    (hc : ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        (c - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ) ∧
        (ramseyR3 k : ℝ) ≤ (c + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)))
    (hup : ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        (ramseyR3 k : ℝ) ≤ (1 + ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)))
    (hlow : ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ k : ℕ, N₀ ≤ k →
        (1 / 2 - ε) * ((k : ℝ) ^ 2 / Real.log (k : ℝ)) ≤ (ramseyR3 k : ℝ)) :
    1 / 2 ≤ c ∧ c ≤ 1 := by
  have hf : ∀ k : ℕ, 2 ≤ k → 0 < (k : ℝ) ^ 2 / Real.log (k : ℝ) := by
    intro k hk
    have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
    exact div_pos (by positivity) (Real.log_pos (by linarith))
  constructor
  · by_contra h
    push_neg at h
    have hε : 0 < (1 / 2 - c) / 4 := by linarith
    obtain ⟨N₁, h₁⟩ := hc _ hε
    obtain ⟨N₂, h₂⟩ := hlow _ hε
    have hk1 : N₁ ≤ max (max N₁ N₂) 2 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hk2 : N₂ ≤ max (max N₁ N₂) 2 := le_trans (le_max_right _ _) (le_max_left _ _)
    have hpos := hf _ (le_max_right (max N₁ N₂) 2)
    have hab := le_trans (h₂ _ hk2) (h₁ _ hk1).2
    have := le_of_mul_le_mul_right hab hpos
    linarith
  · by_contra h
    push_neg at h
    have hε : 0 < (c - 1) / 4 := by linarith
    obtain ⟨N₁, h₁⟩ := hc _ hε
    obtain ⟨N₂, h₂⟩ := hup _ hε
    have hk1 : N₁ ≤ max (max N₁ N₂) 2 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hk2 : N₂ ≤ max (max N₁ N₂) 2 := le_trans (le_max_right _ _) (le_max_left _ _)
    have hpos := hf _ (le_max_right (max N₁ N₂) 2)
    have hab := le_trans (h₁ _ hk1).1 (h₂ _ hk2)
    have := le_of_mul_le_mul_right hab hpos
    linarith

end
