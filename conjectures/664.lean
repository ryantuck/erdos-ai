import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

noncomputable section

/-!
# Erdős Problem #664

Let c < 1 be some constant and A₁, …, Aₘ ⊆ {1, …, n} be such that |Aᵢ| > c√n for all i
and |Aᵢ ∩ Aⱼ| ≤ 1 for all i ≠ j.

Must there exist some set B such that B ∩ Aᵢ ≠ ∅ and |B ∩ Aᵢ| ≪_c 1 for all i?

This was disproved by Alon, who showed that for c = 2/5 and appropriate families derived
from random subsets of lines of a projective plane, any transversal B must intersect
some Aⱼ in Ω(log n) points.
-/

/--
Erdős Problem #664 (Disproved) [Er81][Er97f]:

There exists c ∈ (0, 1) such that for any bound K, there exist n, m and a family
A : Fin m → Finset (Fin n) with |A i| > c√n for all i and |A i ∩ A j| ≤ 1 for i ≠ j,
such that for every transversal B (meeting every A i), there exists some j
with |B ∩ A j| > K.

Proved by Alon using random subsets of lines of a projective plane, with c = 2/5.
-/
theorem erdos_problem_664 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ K : ℕ, ∃ n m : ℕ, ∃ A : Fin m → Finset (Fin n),
      (∀ i, (↑(A i).card : ℝ) > c * Real.sqrt ↑n) ∧
      (∀ i j, i ≠ j → ((A i) ∩ (A j)).card ≤ 1) ∧
      ∀ B : Finset (Fin n),
        (∀ i, ((A i) ∩ B).Nonempty) →
        ∃ j, ((A j) ∩ B).card > K :=
  sorry

end
