import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

noncomputable section

open Classical

/-!
# Erdős Problem #958

Let $A \subset \mathbb{R}^2$ be a finite set of size $n$, and let $\{d_1, \ldots, d_k\}$
be the set of distinct distances determined by $A$. Let $f(d)$ be the multiplicity of $d$,
the number of unordered pairs from $A$ at distance $d$ apart.

Is it true that $k = n - 1$ and $\{f(d_i)\} = \{1, \ldots, n-1\}$ if and only if $A$ is
a set of equidistant points on a line or a circle?

Erdős conjectured that the answer is no, and other such configurations exist [Er84c].

This was proved by Clemen, Dumitrescu, and Liu [CDL25], who observed that equidistant
points on a short circular arc on a circle of radius 1, together with the centre, provide
a counterexample.
-/

/-- The set of distinct distances determined by a finite point set in R². -/
noncomputable def distinctDistances958 (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2)).image (fun p => dist p.1 p.2)

/-- The number of unordered pairs in A at distance d. -/
noncomputable def distMultiplicity958 (A : Finset (EuclideanSpace ℝ (Fin 2))) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = d)).card / 2

/-- The distance multiplicity property: A has exactly n−1 distinct distances and the
    multiplicities are exactly {1, 2, …, n−1}. -/
def HasDistanceMultiplicityProperty958 (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card ≥ 2 ∧
  (distinctDistances958 A).card = A.card - 1 ∧
  ∀ m : ℕ, (1 ≤ m ∧ m ≤ A.card - 1) ↔
    (∃ d ∈ distinctDistances958 A, distMultiplicity958 A d = m)

/-- A finite point set is equidistant-collinear if the points are equally spaced along a
    line: A = {p, p + v, p + 2v, …, p + (n−1)v} for some p, v with v ≠ 0. -/
def IsEquidistantCollinear958 (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (p v : EuclideanSpace ℝ (Fin 2)), v ≠ 0 ∧
    ∀ a ∈ A, ∃ i : Fin A.card, a = p + (i.val : ℝ) • v

/-- A finite point set is equidistant-circular if the points are equally spaced on a
    circle: all points lie on a circle and consecutive points in a cyclic ordering have
    equal Euclidean distance. -/
def IsEquidistantCircular958 (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card ≥ 3 ∧
  ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), r > 0 ∧
    (∀ a ∈ A, dist a c = r) ∧
    ∃ (σ : ℕ → EuclideanSpace ℝ (Fin 2)),
      (∀ i, i < A.card → σ i ∈ A) ∧
      (∀ a ∈ A, ∃ i, i < A.card ∧ σ i = a) ∧
      (∀ i j, i < A.card → j < A.card → σ i = σ j → i = j) ∧
      ∀ i, i < A.card →
        dist (σ i) (σ ((i + 1) % A.card)) = dist (σ 0) (σ 1)

/--
**Erdős Problem #958** [Er84c]:

Erdős conjectured that there exists a finite set A ⊂ R² satisfying the distance
multiplicity property (exactly n−1 distinct distances with multiplicities {1,…,n−1})
that is neither a set of equidistant points on a line nor equidistant points on a circle.

This was proved by Clemen, Dumitrescu, and Liu [CDL25].
-/
theorem erdos_problem_958 :
    ∃ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      HasDistanceMultiplicityProperty958 A ∧
      ¬IsEquidistantCollinear958 A ∧
      ¬IsEquidistantCircular958 A :=
  sorry

end
