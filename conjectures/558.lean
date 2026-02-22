import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Sum

noncomputable section

/-!
# Erdős Problem #558

Let R_k(G) denote the minimal m such that if the edges of K_m are k-coloured
then there is a monochromatic copy of G. Determine
  R_k(K_{s,t})
where K_{s,t} is the complete bipartite graph with s vertices in one part
and t in the other.

Chung and Graham [ChGr75] prove the general bounds
  (2π√(st))^{1/(s+t)} · (s+t)/e² · k^{(st-1)/(s+t)} ≤ R_k(K_{s,t})
    ≤ (t-1)(k + k^{1/s})^s
and determined R_k(K_{2,2}) = (1+o(1))k².

Alon, Rónyai, and Szabó [ARS99] proved that R_k(K_{3,3}) = (1+o(1))k³
and that if s ≥ (t-1)! + 1 then R_k(K_{s,t}) ≍ k^t.
-/

/-- The k-colour Ramsey number R_k(G): the minimum N such that for every
    k-colouring of the edges of K_N, there is a monochromatic copy of G.

    A k-colouring is a symmetric function c : Fin N → Fin N → Fin k.
    A monochromatic copy of G in colour a is an injective map f : V → Fin N
    such that every edge of G maps to an edge of colour a. -/
noncomputable def multicolorRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a : Fin k) (f : V → Fin N), Function.Injective f ∧
      ∀ u v, G.Adj u v → c (f u) (f v) = a}

/--
Erdős Problem #558, Chung-Graham result [ChGr75]:

R_k(K_{2,2}) = (1+o(1))k², i.e., for every ε > 0, there exists K₀
such that for all k ≥ K₀,
  (1 - ε)k² ≤ R_k(K_{2,2}) ≤ (1 + ε)k².
-/
theorem erdos_problem_558_K22 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (1 - ε) * (k : ℝ) ^ 2 ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin 2) (Fin 2)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin 2) (Fin 2)) k : ℝ) ≤
        (1 + ε) * (k : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #558, Alon-Rónyai-Szabó result [ARS99]:

R_k(K_{3,3}) = (1+o(1))k³, i.e., for every ε > 0, there exists K₀
such that for all k ≥ K₀,
  (1 - ε)k³ ≤ R_k(K_{3,3}) ≤ (1 + ε)k³.
-/
theorem erdos_problem_558_K33 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (1 - ε) * (k : ℝ) ^ 3 ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin 3) (Fin 3)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin 3) (Fin 3)) k : ℝ) ≤
        (1 + ε) * (k : ℝ) ^ 3 :=
  sorry

/--
Erdős Problem #558, Alon-Rónyai-Szabó result [ARS99]:

If s ≥ (t-1)! + 1 then R_k(K_{s,t}) ≍ k^t, i.e., there exist constants
C₁, C₂ > 0 such that for all sufficiently large k,
  C₁ · k^t ≤ R_k(K_{s,t}) ≤ C₂ · k^t.
-/
theorem erdos_problem_558_ars (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ 1)
    (hst : s ≥ Nat.factorial (t - 1) + 1) :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      C₁ * (k : ℝ) ^ t ≤
        (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ∧
      (multicolorRamseyNumber (completeBipartiteGraph (Fin s) (Fin t)) k : ℝ) ≤
        C₂ * (k : ℝ) ^ t :=
  sorry

end
