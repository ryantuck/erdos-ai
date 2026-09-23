-- [AI-Generated]: Erdős Problem 1105 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1105

*Source:* [erdosproblems.com/1105](https://www.erdosproblems.com/1105) (status **PROVED**:
"This has been solved in the affirmative."; page last edited 29 January 2026, captured
2026-03-09). [ESS75]

The anti-Ramsey number AR(n,G) is the maximum possible number of colours in
which the edges of K_n can be coloured without creating a rainbow copy of G
(i.e. one in which all edges have different colours).

Let C_k be the cycle on k vertices. Is it true that
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) n + O(1)?

Let P_k be the path on k vertices and ℓ = ⌊(k-1)/2⌋. If n ≥ k ≥ 5 then is
AR(n, P_k) equal to
  max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ε = 1 if k is odd and ε = 2 otherwise?

A conjecture of Erdős, Simonovits, and Sós [ESS75], who gave a simple proof that
AR(n, C_3) = n - 1. In [ESS75] they announced proofs of the path formula for
n ≥ (5/4)k + C (some large constant C), and for all n ≥ k when k is sufficiently large,
but these never appeared. Simonovits and Sós [SiSo84] published a proof of the path
formula for n ≥ ck² for some constant c > 0. A proof of the path formula for all
n ≥ k ≥ 5 has been announced by Yuan [Yu21]. Montellano-Ballesteros and Neumann-Lara
[MoNe05] gave an exact formula for AR(n, C_k), which implies the cycle formula.

Both questions are answered "yes"; the two main theorems state the true direction.

Tags: graph theory, ramsey theory. OEIS: "possible" at capture (A399683, A399687 in the
teorth/erdosproblems mirror). The page records an upstream formalised statement.

## References

* [ESS75] Erdős, P. and Simonovits, M. and Sós, V. T., _Anti-Ramsey theorems_. (1975),
  633–643.
* [MoNe05] Montellano-Ballesteros, J. J. and Neumann-Lara, V., _An anti-Ramsey theorem on
  cycles_. Graphs Combin. (2005), 343–354.
* [SiSo84] Simonovits, Miklós and Sós, Vera T., _On restricted colourings of K_n_.
  Combinatorica (1984), 101–110.
* [Yu21] L.-T. Yuan, _The anti-Ramsey number for paths_. arXiv:2102.00807 (2021).

(As carried by the upstream formal-conjectures `ErdosProblems/1105.lean` captured in this
repository's logs; no `/latex/1105` fetch survives. Proceedings and volume data are not
recorded there.)
-/

/-- An edge-coloring of K_n contains a rainbow copy of G if there is an
    injection from V(G) to Fin n such that the coloring assigns distinct
    colors to all edge-images of G. (Only the values of `c` on non-diagonal elements of
    `Sym2 (Fin n)`, i.e. on edges of K_n, can matter here, since an injective `φ` maps
    every edge of `G` to an edge of K_n.) -/
def HasRainbowCopy {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (c : Sym2 (Fin n) → ℕ) : Prop :=
  ∃ (φ : V ↪ Fin n), Function.Injective
    (fun (e : G.edgeSet) => c (Sym2.map φ e.val))

/-- The anti-Ramsey number AR(n, G): the maximum number of distinct colors
    used on the edges of K_n by an edge-coloring of K_n that avoids a rainbow copy of G.

    Only the colours on the edges of K_n, `(⊤ : SimpleGraph (Fin n)).edgeSet`, are
    counted. The first-pass file counted `Set.range c` over all of `Sym2 (Fin n)`,
    including the n diagonal elements `s(i, i)`, which are not edges. Colouring those with
    n fresh colours never creates a rainbow copy, so that definition equals AR(n, G) + n.
    For example it gives 7 for (n, G) = (4, C_3), whose true value is 3, and it made both
    main theorems false. -/
noncomputable def antiRamseyNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (c : Sym2 (Fin n) → ℕ),
    Set.ncard (c '' (⊤ : SimpleGraph (Fin n)).edgeSet) = k ∧ ¬HasRainbowCopy G n c}

/-- The path graph on k vertices: Fin k with edges {i, i+1}. -/
def pathGraph1105 (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm _ _ h := h.elim Or.inr Or.inl
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

/-- The cycle graph on k vertices: Fin k with edges between consecutive
    vertices modulo k (vertex i adjacent to (i+1) mod k). This is C_k for k ≥ 3. -/
def cycleGraph1105 (k : ℕ) : SimpleGraph (Fin k) where
  Adj i j := i ≠ j ∧ ((i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val)
  symm _ _ h := ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/--
Erdős Problem #1105 (Cycles) [ESS75] (PROVED):

The anti-Ramsey number for cycles satisfies
  AR(n, C_k) = ((k-2)/2 + 1/(k-1)) n + O(1).

Proved by Montellano-Ballesteros and Neumann-Lara [MoNe05]. (The O(1) constant depends
on k; requiring the bound for every n ≥ k rather than eventually is equivalent, since
finitely many n can be absorbed into C.)
-/
theorem erdos_problem_1105_cycles (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, C ≥ 0 ∧ ∀ n : ℕ, n ≥ k →
      |(↑(antiRamseyNumber (cycleGraph1105 k) n) : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * (n : ℝ)| ≤ C :=
  sorry

/--
Erdős Problem #1105 (Paths) [ESS75] (PROVED):

For n ≥ k ≥ 5, the anti-Ramsey number for paths is
  AR(n, P_k) = max(C(k-2,2) + 1, C(ℓ-1,2) + (ℓ-1)(n-ℓ+1) + ε)
where ℓ = ⌊(k-1)/2⌋ and ε = 1 if k is odd, ε = 2 otherwise.

Proof announced by Yuan [Yu21]. (All natural-number subtractions are exact here, since
k ≥ 5 gives ℓ ≥ 2 and n ≥ k > ℓ. Example: k = n = 5 gives max(4, 5) = 5, which matches
a brute-force computation of AR(5, P_5).)
-/
theorem erdos_problem_1105_paths (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    antiRamseyNumber (pathGraph1105 k) n =
      let ℓ := (k - 1) / 2
      let ε := if k % 2 = 1 then 1 else 2
      max (Nat.choose (k - 2) 2 + 1)
        (Nat.choose (ℓ - 1) 2 + (ℓ - 1) * (n - ℓ + 1) + ε) :=
  sorry

/-- [ESS75] (solved): AR(n, C_3) = n - 1 (the rainbow-triangle case, with a simple proof
by Erdős, Simonovits and Sós). -/
theorem erdos_problem_1105.variants.triangle (n : ℕ) (hn : 3 ≤ n) :
    antiRamseyNumber (cycleGraph1105 3) n = n - 1 :=
  sorry

/-- [SiSo84] (solved): the path formula holds for n ≥ c·k² for some constant c > 0. This
is the published partial result preceding Yuan's announced proof for all n ≥ k ≥ 5. -/
theorem erdos_problem_1105.variants.simonovits_sos :
    ∃ c : ℝ, c > 0 ∧ ∀ k n : ℕ, 5 ≤ k → c * (k : ℝ) ^ 2 ≤ (n : ℝ) →
      antiRamseyNumber (pathGraph1105 k) n =
        let ℓ := (k - 1) / 2
        let ε := if k % 2 = 1 then 1 else 2
        max (Nat.choose (k - 2) 2 + 1)
          (Nat.choose (ℓ - 1) 2 + (ℓ - 1) * (n - ℓ + 1) + ε) :=
  sorry

end
