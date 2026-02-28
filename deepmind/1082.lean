/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1082

*Reference:* [erdosproblems.com/1082](https://www.erdosproblems.com/1082)

A conjecture of Szemerédi, who proved the result with $\lfloor n/2 \rfloor$ replaced by
$n/3$. More generally, Szemerédi gave a simple proof that if there are no $k$ points on a
line then some point determines $\gg n/k$ distinct distances.

[Er75f] Erdős, P., *Problems and results on combinatorial geometry*, 1975, p. 101.
-/

namespace Erdos1082

/-- No three points in the finite set are collinear. -/
def NoThreeCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, p ≠ q → p ≠ r → q ≠ r →
    ¬Collinear ℝ ({(p : EuclideanSpace ℝ (Fin 2)), q, r} : Set (EuclideanSpace ℝ (Fin 2)))

/-- The number of distinct pairwise distances determined by a finite point set in $\mathbb{R}^2$. -/
noncomputable def distinctDistanceCount2d (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ d = dist p q}

/--
**Erdős Problem 1082** [Er75f, p.101]:

Let $A \subset \mathbb{R}^2$ be a set of $n$ points with no three on a line. Then $A$ determines
at least $\lfloor n/2 \rfloor$ distinct distances.
-/
@[category research open, AMS 52]
theorem erdos_1082
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (hP : NoThreeCollinear P) :
    distinctDistanceCount2d P ≥ P.card / 2 := by
  sorry

end Erdos1082
