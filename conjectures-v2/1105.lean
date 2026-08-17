import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1105

The anti-Ramsey number AR(n,G) is the maximum possible number of colours in
which the edges of K_n can be coloured without creating a rainbow copy of G
(i.e. one in which all edges have different colours).

Let C_k be the cycle on k vertices. Is it true that
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) n + O(1)?

Let P_k be the path on k vertices and ℓ = ⌊(k-1)/2⌋. If n ≥ k ≥ 5 then is
AR(n, P_k) equal to
  max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ε = 1 if k is odd and ε = 2 otherwise?

A conjecture of Erdős, Simonovits, and Sós [ESS75], who gave a simple proof
that AR(n, C_3) = n - 1. In that paper they announced proofs of the claimed
formula for AR(n, P_k) for n ≥ (5/4)k + C for some large constant C, and also
for all n ≥ k if k is sufficiently large, but these never appeared.
Simonovits and Sós [SiSo84] published a proof that the claimed formula for
AR(n, P_k) is true for n ≥ ck² for some constant c > 0. A proof of the
formula for AR(n, P_k) for all n ≥ k ≥ 5 has been announced by Yuan [Yu21].
Montellano-Ballesteros and Neumann-Lara [MoNe05] gave an exact formula for
AR(n, C_k), which implies in particular that
AR(n, C_k) = ((k-2)/2 + 1/(k-1)) n + O(1).

Status (erdosproblems.com, page edition 29 January 2026, accessed
2026-03-09): PROVED — "This has been solved in the affirmative."

References (honest stubs; volume numbers not recoverable offline):
- [ESS75] Erdős, P. and Simonovits, M. and Sós, V. T., Anti-Ramsey theorems.
  (1975), 633–643.
- [SiSo84] Simonovits, Miklós and Sós, Vera T., On restricted colourings of
  K_n. Combinatorica (1984), 101–110.
- [MoNe05] Montellano-Ballesteros, J. J. and Neumann-Lara, V., An
  anti-Ramsey theorem on cycles. Graphs Combin. (2005), 343–354.
- [Yu21] L.-T. Yuan, The anti-Ramsey number for paths. arXiv:2102.00807
  (2021).

https://www.erdosproblems.com/1105
Tags: graph theory, ramsey theory
-/

/-- An edge-coloring of K_n contains a rainbow copy of G if there is an
    injection from V(G) to Fin n such that the coloring assigns distinct
    colors to all edge-images of G. -/
def HasRainbowCopy {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (c : Sym2 (Fin n) → ℕ) : Prop :=
  ∃ (φ : V ↪ Fin n), Function.Injective
    (fun (e : G.edgeSet) => c (Sym2.map φ e.val))

/-- The anti-Ramsey number AR(n, G): the maximum number of distinct colors
    used in an edge-coloring of K_n that avoids a rainbow copy of G.

    Colors are counted only on the non-diagonal elements of `Sym2 (Fin n)`,
    i.e. on the actual edges of K_n; the values of `c` on diagonal (loop)
    pairs are ignored. (Counting `Set.range c` instead would inflate the
    supremum by exactly n for n ≥ 1, since a coloring may spend n fresh
    colors on the loops without ever creating a rainbow copy.) -/
noncomputable def antiRamseyNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (c : Sym2 (Fin n) → ℕ),
    Set.ncard (c '' {e : Sym2 (Fin n) | ¬e.IsDiag}) = k ∧ ¬HasRainbowCopy G n c}

/-- The path graph on k vertices: Fin k with edges {i, i+1}. -/
def pathGraph1105 (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm _ _ h := h.elim Or.inr Or.inl
  loopless := fun _ h => by rcases h with h | h <;> omega

/-- The cycle graph on k vertices: Fin k with edges between consecutive
    vertices modulo k (vertex i adjacent to (i+1) mod k). -/
def cycleGraph1105 (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ ((i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)
  symm _ _ h := ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩
  loopless := fun _ h => h.1 rfl

/--
Erdős Problem #1105 (Cycles) [ESS75]:

The anti-Ramsey number for cycles satisfies
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) n + O(1).

Montellano-Ballesteros and Neumann-Lara [MoNe05] gave an exact formula for
AR(n, C_k), which implies this asymptotic formula in particular.
-/
theorem erdos_problem_1105_cycles (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ n : ℕ, n ≥ k →
      |(↑(antiRamseyNumber (cycleGraph1105 k) n) : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ)| ≤ C :=
  sorry

/--
Erdős Problem #1105 (Paths) [ESS75]:

For n ≥ k ≥ 5, the anti-Ramsey number for paths is
  AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋ and ε = 1 if k is odd, ε = 2 otherwise.

A proof for all n ≥ k ≥ 5 has been announced by Yuan [Yu21].
-/
theorem erdos_problem_1105_paths (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    antiRamseyNumber (pathGraph1105 k) n =
      let ℓ := (k - 1) / 2
      let ε := if k % 2 = 1 then 1 else 2
      max (Nat.choose (k - 2) 2 + 1)
        (Nat.choose (ℓ - 1) 2 + (ℓ - 1) * (n - ℓ + 1) + ε) :=
  sorry

/--
Erdős Problem #1105 (Triangles variant) [ESS75]:

Erdős, Simonovits, and Sós gave a simple proof that AR(n, C_3) = n - 1.
-/
theorem erdos_problem_1105_triangles (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNumber (cycleGraph1105 3) n = n - 1 :=
  sorry

/--
Erdős Problem #1105 (Paths, quadratic range variant) [SiSo84]:

Simonovits and Sós published a proof that the claimed formula for AR(n, P_k)
is true for n ≥ ck² for some constant c > 0.
-/
theorem erdos_problem_1105_paths_quadratic :
    ∃ c : ℝ, 0 < c ∧ ∀ k n : ℕ, 5 ≤ k → c * (k : ℝ) ^ 2 ≤ (n : ℝ) →
      antiRamseyNumber (pathGraph1105 k) n =
        let ℓ := (k - 1) / 2
        let ε := if k % 2 = 1 then 1 else 2
        max (Nat.choose (k - 2) 2 + 1)
          (Nat.choose (ℓ - 1) 2 + (ℓ - 1) * (n - ℓ + 1) + ε) :=
  sorry

end
