import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #223

Let $d \geq 2$ and $n \geq 2$. Let $f_d(n)$ be maximal such that there exists
some set of $n$ points $A \subseteq \mathbb{R}^d$, with diameter $1$, in which
the distance $1$ occurs between $f_d(n)$ many pairs of points in $A$.
Estimate $f_d(n)$.

Originally a conjecture of Vázsonyi [Er46b].

Known results:
- Hopf and Pannwitz [HoPa34] proved $f_2(n) = n$.
- Grünbaum [Gr56], Heppes [He56], and Strasziewicz [St57] showed $f_3(n) = 2n - 2$.
- Erdős [Er60b] proved that for $d \geq 4$,
  $f_d(n) = \left(\frac{p-1}{2p} + o(1)\right) n^2$ where $p = \lfloor d/2 \rfloor$.
- Swanepoel [Sw09] gave exact values for all $d \geq 4$ and sufficiently large $n$.
-/

/-- The number of unordered pairs {x, y} in A with x ≠ y and dist x y = 1.
    Defined as half the ordered pair count (always even by symmetry of dist). -/
noncomputable def unitDistPairs {d : ℕ} (A : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = 1)).card / 2

/--
Erdős Problem #223 (d = 2), Hopf–Pannwitz [HoPa34]:
Among n points in ℝ² with all pairwise distances ≤ 1, the distance 1
occurs between at most n pairs.
-/
theorem erdos223_d2_upper (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    unitDistPairs A ≤ A.card :=
  sorry

/--
Erdős Problem #223 (d = 2), tightness:
For every n ≥ 2, there exist n points in ℝ² with diameter 1 and
exactly n pairs at distance 1.
-/
theorem erdos223_d2_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n ∧
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
      unitDistPairs A = n :=
  sorry

/--
Erdős Problem #223 (d = 3), Grünbaum–Heppes–Strasziewicz [Gr56, He56, St57]:
Among n ≥ 2 points in ℝ³ with all pairwise distances ≤ 1, the distance 1
occurs between at most 2n - 2 pairs.
-/
theorem erdos223_d3_upper (A : Finset (EuclideanSpace ℝ (Fin 3)))
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1)
    (hcard : 2 ≤ A.card) :
    unitDistPairs A ≤ 2 * A.card - 2 :=
  sorry

/--
Erdős Problem #223 (d = 3), tightness:
For every n ≥ 2, there exist n points in ℝ³ with diameter 1 and
exactly 2n - 2 pairs at distance 1.
-/
theorem erdos223_d3_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 3)),
      A.card = n ∧
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
      unitDistPairs A = 2 * n - 2 :=
  sorry

/--
Erdős Problem #223 (d ≥ 4), upper bound — Erdős [Er60b]:
For d ≥ 4, let p = ⌊d/2⌋. For every ε > 0, for sufficiently large n,
any n points in ℝ^d of diameter ≤ 1 have at most ((p-1)/(2p) + ε)n²
unit-distance pairs.
-/
theorem erdos223_d_ge4_upper (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin d))),
      N₀ ≤ A.card →
      (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) →
      (unitDistPairs A : ℝ) ≤
        ((↑(d / 2) - 1) / (2 * ↑(d / 2)) + ε) * (A.card : ℝ) ^ 2 :=
  sorry

/--
Erdős Problem #223 (d ≥ 4), lower bound — Erdős [Er60b]:
For d ≥ 4, let p = ⌊d/2⌋. For every ε > 0, for sufficiently large n,
there exist n points in ℝ^d of diameter ≤ 1 with at least
((p-1)/(2p) - ε)n² unit-distance pairs.
-/
theorem erdos223_d_ge4_lower (d : ℕ) (hd : 4 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ A : Finset (EuclideanSpace ℝ (Fin d)),
        A.card = n ∧
        (∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) ∧
        ((↑(d / 2) - 1) / (2 * ↑(d / 2)) - ε) * (n : ℝ) ^ 2 ≤ (unitDistPairs A : ℝ) :=
  sorry
