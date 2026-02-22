import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #555

Let R_k(G) denote the minimal m such that if the edges of K_m are k-coloured
then there is a monochromatic copy of G. Determine the value of
  R_k(C_{2n}).

A problem of Erdős and Graham. Erdős [Er81c] gives the bounds
  k^{1 + 1/(2n)} ≪ R_k(C_{2n}) ≪ k^{1 + 1/(n-1)}.

Chung and Graham [ChGr75] showed that
  R_k(C_4) > k² - k + 1  when k-1 is a prime power, and
  R_k(C_4) ≤ k² + k + 1  for all k.
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

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
Erdős Problem #555, lower bound [Er81c]:

For every n ≥ 2, there exist C > 0 and K₀ such that for all k ≥ K₀,
  R_k(C_{2n}) ≥ C · k^{1 + 1/(2n)}.
-/
theorem erdos_problem_555_lower (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n) (by omega)) k : ℝ) ≥
        C * (k : ℝ) ^ ((1 : ℝ) + 1 / (2 * (n : ℝ))) :=
  sorry

/--
Erdős Problem #555, upper bound [Er81c]:

For every n ≥ 2, there exist C > 0 and K₀ such that for all k ≥ K₀,
  R_k(C_{2n}) ≤ C · k^{1 + 1/((n : ℝ) - 1)}.
-/
theorem erdos_problem_555_upper (n : ℕ) (hn : n ≥ 2) :
    ∃ C : ℝ, C > 0 ∧ ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n) (by omega)) k : ℝ) ≤
        C * (k : ℝ) ^ ((1 : ℝ) + 1 / ((n : ℝ) - 1)) :=
  sorry

/--
Chung-Graham upper bound [ChGr75]: R_k(C_4) ≤ k² + k + 1 for all k ≥ 2.
-/
theorem erdos_problem_555_chung_graham_upper (k : ℕ) (hk : k ≥ 2) :
    multicolorRamseyNumber (cycleGraph 4 (by omega)) k ≤ k ^ 2 + k + 1 :=
  sorry

end
