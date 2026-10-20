-- [AI - Claude Opus 5.5]: Erdős Problem 174 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #174 (Euclidean Ramsey sets)

*Source:* [erdosproblems.com/174](https://www.erdosproblems.com/174) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-02-20; page edited 16 October
2025). [Er75f, p.108] [ErGr79] [ErGr80] [Er83c]

A finite set $A\subset \mathbb{R}^n$ is called Ramsey if, for any $k\geq 1$, there exists some
$d=d(A,k)$ such that in any $k$-colouring of $\mathbb{R}^d$ there exists a monochromatic copy of
$A$. Characterise the Ramsey sets in $\mathbb{R}^n$.

Remarks recorded on the page: Erdős, Graham, Montgomery, Rothschild, Spencer, and Straus [EGMRSS73]
proved that every Ramsey set is 'spherical': it lies on the surface of some sphere. Graham has
conjectured that every spherical set is Ramsey. Leader, Russell, and Walters [LRW12] have
alternatively conjectured that a set is Ramsey if and only if it is 'subtransitive': it can be
embedded in some higher-dimensional set on which rotations act transitively. Sets known to be
Ramsey include vertices of $k$-dimensional rectangles [EGMRSS73], non-degenerate simplices [FrRo90],
trapezoids [Kr92], and regular polygons/polyhedra [Kr91].

## Encoding notes

* "Characterise" has no single formal target. The main theorem asserts Graham's characterisation
  (Ramsey ⟺ spherical), labelled as such; the page also records the alternative of [LRW12]
  (`variants.leader_russell_walters`). Given the proved direction [EGMRSS73], the main theorem is
  exactly Graham's conjecture (`variants.main_iff_graham`, PROVED).
* A "copy" of `A` is its image under a distance-preserving map of all of `ℝⁿ` into `ℝᵈ`. Requiring
  the map on all of `ℝⁿ` costs nothing: a distance-preserving map on `A` extends to `ℝⁿ` once
  `d ≥ n`, and `d` is chosen existentially (the property only gets easier as `d` grows).
* Checks (PROVED in Lean): the empty set is Ramsey (`isEuclideanRamsey_empty`); three collinear
  points `0, 1, 2` on a line are not spherical (`not_isSpherical_collinear`), so `IsSpherical` is
  not vacuous, and the main theorem says such a set is not Ramsey, as [EGMRSS73] proved.

## References

From the site's `/latex/174` bibliography:
* [EGMRSS73] Erdős, P., Graham, R. L., Montgomery, P., Rothschild, B. L., Spencer, J. and Straus,
  E. G., _Euclidean Ramsey theorems I_. J. Combin. Theory Ser. A (1973), 341–363.
* [FrRo90] Frankl, P. and Rödl, V., _A partition property of simplices in Euclidean space_. J. Amer.
  Math. Soc. (1990), 1–7.
* [Kr91] Kříž, I., _Permutation groups in Euclidean Ramsey theory_. Proc. Amer. Math. Soc. (1991),
  899–907.
* [Kr92] Kříž, I., _All trapezoids are Ramsey_. Discrete Math. (1992), 59–62.
* [LRW12] Leader, I., Russell, P. A. and Walters, M., _Transitive sets in Euclidean Ramsey theory_.
  J. Combin. Theory Ser. A (2012), 382–396.

Erdős's sources:
* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat. Pura
  Appl. (4) (1975), 99–108. (Site `/latex/1090` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54. (Site
  `/latex/217`.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/174.lean` (Opus 5.5 review, `opus-5-5-review/174.md`).
-/

/-- A finite subset A of ℝⁿ is Euclidean Ramsey if for every k ≥ 1, there
    exists d such that any k-coloring of ℝᵈ contains a monochromatic
    isometric copy of A (i.e., a copy obtained by a distance-preserving map). -/
def IsEuclideanRamsey (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∃ d : ℕ, ∀ f : EuclideanSpace ℝ (Fin d) → Fin k,
      ∃ φ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d),
        (∀ x y, dist (φ x) (φ y) = dist x y) ∧
        ∃ c : Fin k, ∀ a ∈ A, f (φ a) = c

/-- A finite set in ℝⁿ is spherical if all its points lie on the surface
    of some sphere (are equidistant from some center point). -/
def IsSpherical (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (center : EuclideanSpace ℝ (Fin n)) (r : ℝ),
    ∀ a ∈ A, dist a center = r

/--
Erdős Problem #174 / Graham's Conjecture:
A finite set A ⊂ ℝⁿ is Ramsey if and only if it is spherical.

The forward direction (Ramsey → spherical) was proved by Erdős, Graham,
Montgomery, Rothschild, Spencer, and Straus [EGMRSS73].

The reverse direction (spherical → Ramsey) is Graham's open conjecture.
(Status: OPEN. The page asks to characterise the Ramsey sets; this is Graham's proposed
characterisation, and [LRW12] proposes another.)
-/
theorem erdos_problem_174 :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A ↔ IsSpherical n A :=
  sorry

/-- Erdős, Graham, Montgomery, Rothschild, Spencer and Straus [EGMRSS73] (SOLVED; not proved here):
every Ramsey set is spherical. -/
theorem erdos_problem_174.variants.spherical_of_ramsey :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A → IsSpherical n A :=
  sorry

/-- Graham's conjecture (OPEN): every spherical set is Ramsey. -/
theorem erdos_problem_174.variants.graham :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsSpherical n A → IsEuclideanRamsey n A :=
  sorry

/-- Given the proved direction, the main theorem is exactly Graham's conjecture (PROVED in Lean). -/
theorem erdos_problem_174.variants.main_iff_graham
    (hfw : ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A → IsSpherical n A) :
    (∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A ↔ IsSpherical n A) ↔
    (∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsSpherical n A → IsEuclideanRamsey n A) :=
  ⟨fun h n A => (h n A).mpr, fun h n A => ⟨hfw n A, h n A⟩⟩

/-- The empty set is Ramsey (PROVED in Lean). -/
theorem erdos_problem_174.isEuclideanRamsey_empty (n : ℕ) : IsEuclideanRamsey n ∅ := by
  intro k hk
  refine ⟨n, fun f => ⟨id, fun x y => rfl, ⟨0, hk⟩, by simp⟩⟩

open Classical in
/-- The collinear points `0, 1, 2` of `ℝ¹` are not spherical (PROVED in Lean): a centre `x`
would satisfy `|x| = |1 - x| = |2 - x|`. -/
theorem erdos_problem_174.not_isSpherical_collinear :
    ¬ IsSpherical 1 {EuclideanSpace.single 0 0, EuclideanSpace.single 0 1,
      EuclideanSpace.single 0 2} := by
  rintro ⟨c, r, h⟩
  have key : ∀ t : ℝ, dist (EuclideanSpace.single (0 : Fin 1) t) c = |t - c 0| := by
    intro t
    rw [EuclideanSpace.dist_eq, Fin.sum_univ_one, EuclideanSpace.single_apply, if_pos rfl,
      Real.sqrt_sq_eq_abs, Real.dist_eq, abs_abs]
  have h0 := h (EuclideanSpace.single 0 0) (by simp)
  have h1 := h (EuclideanSpace.single 0 1) (by simp)
  have h2 := h (EuclideanSpace.single 0 2) (by simp)
  rw [key] at h0 h1 h2
  have e1 : |(0 : ℝ) - c 0| = |1 - c 0| := h0.trans h1.symm
  have e2 : |(1 : ℝ) - c 0| = |2 - c 0| := h1.trans h2.symm
  have q1 : ((0 : ℝ) - c 0) ^ 2 = (1 - c 0) ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) e1
    simpa only [sq_abs] using this
  have q2 : ((1 : ℝ) - c 0) ^ 2 = (2 - c 0) ^ 2 := by
    have := congrArg (fun t : ℝ => t ^ 2) e2
    simpa only [sq_abs] using this
  ring_nf at q1 q2
  linarith

/-- Frankl and Rödl [FrRo90] (SOLVED; not proved here): the vertex set of a non-degenerate simplex
is Ramsey. -/
theorem erdos_problem_174.variants.frankl_rodl :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      AffineIndependent ℝ (fun a : A => (a : EuclideanSpace ℝ (Fin n))) →
      IsEuclideanRamsey n A :=
  sorry

/-- Subtransitivity, as described on the page (review addition): `A` embeds isometrically in a
finite set `B` in some `ℝᵐ` whose symmetries (isometries of `ℝᵐ` mapping `B` into itself) act
transitively on `B`. The exact definition of [LRW12] was not checked. -/
def erdos_problem_174.IsSubtransitive (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ (m : ℕ) (B : Finset (EuclideanSpace ℝ (Fin m)))
    (ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)),
    (∀ x y, dist (ψ x) (ψ y) = dist x y) ∧ (∀ a ∈ A, ψ a ∈ B) ∧
    ∀ b ∈ B, ∀ b' ∈ B, ∃ g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      (∀ x y, dist (g x) (g y) = dist x y) ∧ (∀ x ∈ B, g x ∈ B) ∧ g b = b'

/-- The conjecture of Leader, Russell and Walters [LRW12] (OPEN): a set is Ramsey if and only if it
is subtransitive. -/
theorem erdos_problem_174.variants.leader_russell_walters :
    ∀ n : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin n)),
      IsEuclideanRamsey n A ↔ erdos_problem_174.IsSubtransitive n A :=
  sorry
