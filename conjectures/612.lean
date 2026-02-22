import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic

open Classical SimpleGraph

noncomputable section

/-!
# Erdős Problem #612

Let G be a connected graph with n vertices, minimum degree d, and diameter D.

The original conjecture of Erdős, Pach, Pollack, and Tuza [EPPT89] stated:
- If G contains no K_{2r} and (r-1)(3r+2) ∣ d then
    D ≤ 2(r-1)(3r+2)/(2r²-1) · n/d + O(1)
- If G contains no K_{2r+1} and (3r-1) ∣ d then
    D ≤ (3r-1)/r · n/d + O(1)

The first case was disproven for r ≥ 2 by Czabarka, Singgih, and Székely [CSS21].

The amended conjecture (due to [CSS21]) states that if G contains no K_{k+1} then
  D ≤ (3 − 2/k) · n/d + O(1).

This is known:
- For k = 2 (K_3-free), proved in [EPPT89]
- For 3-colourable graphs (weaker than K_4-free), by Czabarka, Dankelmann,
  Székely [CDS09]
- For 4-colourable graphs (weaker than K_5-free), by Czabarka, Smith,
  Székely [CSS23]

It is also known that any connected graph on n vertices with minimum degree d has
  D ≤ 3n/(d+1) + O(1).

Tags: graph theory
-/

/--
**Erdős Problem #612** (Amended conjecture, Czabarka-Singgih-Székely [CSS21]):

If G is a connected K_{k+1}-free graph on n vertices with minimum degree d ≥ 1,
then
  diam(G) ≤ (3 − 2/k) · n/d + C
for some constant C depending only on k.
-/
theorem erdos_problem_612 (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected →
      G.CliqueFree (k + 1) →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ (3 - 2 / (k : ℝ)) * ((n : ℝ) / (G.minDegree : ℝ)) + C :=
  sorry

/--
**Erdős Problem #612** (Known case k = 2, [EPPT89]):

If G is a connected triangle-free graph on n vertices with minimum degree d ≥ 1,
then
  diam(G) ≤ 2 · n/d + C
for some absolute constant C.
-/
theorem erdos_problem_612_triangle_free :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected →
      G.CliqueFree 3 →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ 2 * ((n : ℝ) / (G.minDegree : ℝ)) + C :=
  sorry

/--
**Known general bound** (see [EPPT89]):

Any connected graph on n vertices with minimum degree d ≥ 1 has
  diam(G) ≤ 3n/(d+1) + O(1).
-/
theorem erdos_problem_612_general_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.Connected →
      G.minDegree ≥ 1 →
      (G.diam : ℝ) ≤ 3 * ((n : ℝ) / ((G.minDegree : ℝ) + 1)) + C :=
  sorry

end
