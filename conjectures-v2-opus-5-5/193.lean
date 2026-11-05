-- [AI - Claude Opus 5.5]: Erdős Problem 193 — second-pass formalization
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum

/-!
# Erdős Problem #193

*Source:* [erdosproblems.com/193](https://www.erdosproblems.com/193) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20).
[ErGr79] [ErGr80]

Let $S\subseteq \mathbb{Z}^3$ be a finite set and let $A=\{a_1,a_2,\ldots,\}\subset \mathbb{Z}^3$ be
an infinite $S$-walk, so that $a_{i+1}-a_i\in S$ for all $i$. Must $A$ contain three collinear
points?

Remarks recorded on the page: originally conjectured by Gerver and Ramsey [GeRa79], who showed that
the answer is yes for $\mathbb{Z}^2$, and for $\mathbb{Z}^3$ that the largest number of collinear
points can be bounded. OEIS A231255.

## Status after capture, and the fix

The metadata mirror (`c443d8c`) records the problem as **disproved (Lean)** (2026-09-04), and
upstream `formal-conjectures` (`2befc3a`) records the answer **no**: Cambie and Kalviainen [CaKa26]
construct an infinite walk in $\mathbb Z^3$ with a finite set of steps and no three collinear
points, with a linked Lean proof (`ekalvi/erdos-193`, `Hilbert193.erdos193_unconditional`).
Neither the paper nor the proof was read in this review.

The input asserted the "yes" answer. v2 states the recorded answer for the input's formulation
(injective walks) and keeps upstream's formulation (walks with infinite range) as a variant.
Upstream's statement refutes the input's only if the counterexample walk is injective; the walk of
[CaKa26] was not inspected, so that step is not checked here.

## Encoding notes

* `Collinear3 p q r` says `q - p` and `r - p` are linearly dependent over `ℤ`, which for integer
  vectors is collinearity. Degenerate triples count (`collinear3_self_right`, PROVED in Lean), so
  the statement needs distinct points; the input's injectivity provides them, since `i < j < k`.

## References

From the site's `/latex/193` bibliography:
* [GeRa79] Gerver, Joseph L. and Ramsey, L. Thomas, _On certain sequences of lattice points_.
  Pacific J. Math. (1979), 357–363.

Other sources:
* [CaKa26] Cambie, Stijn and Kalviainen, Erik, _An infinite small-step $\mathbb Z^3$-walk with no
  collinear triple_. arXiv:2609.01766 (2026). (From upstream's Problem 193 file; not read.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/193.lean` (Opus 5.5 review, `opus-5-5-review/193.md`).
-/

/-- Three points in ℤ³ are collinear if the difference vectors from the first
    to the other two are linearly dependent over ℤ (equivalently, over ℚ). -/
def Collinear3 (p q r : Fin 3 → ℤ) : Prop :=
  ∃ a b : ℤ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ k : Fin 3, a * (q k - p k) = b * (r k - p k)

/--
Erdős Problem #193 [ErGr79, ErGr80], with the answer recorded after the capture: **no**.

There is a finite set S ⊆ ℤ³ and an injective S-walk a : ℕ → ℤ³ whose range contains no three
collinear points.

(Status: OPEN at capture; recorded as disproved by the mirror and upstream [CaKa26], unverified
here, and with the injectivity of the counterexample walk not checked.)
-/
theorem erdos_problem_193 :
    ¬ ∀ (S : Finset (Fin 3 → ℤ)) (a : ℕ → (Fin 3 → ℤ)),
      Function.Injective a →
      (∀ i, a (i + 1) - a i ∈ S) →
      ∃ i j k : ℕ, i < j ∧ j < k ∧ Collinear3 (a i) (a j) (a k) :=
  sorry

/-- Upstream's formulation of the recorded answer (DISPROVED per upstream and the mirror; not proved
here): some walk with finitely many steps and infinite range has no three distinct collinear points. -/
theorem erdos_problem_193.variants.infinite_range_form :
    ∃ (S : Finset (Fin 3 → ℤ)) (a : ℕ → (Fin 3 → ℤ)), (∀ i, a (i + 1) - a i ∈ S) ∧
      (Set.range a).Infinite ∧
      ∀ i j k : ℕ, a i ≠ a j → a j ≠ a k → a i ≠ a k → ¬ Collinear3 (a i) (a j) (a k) :=
  sorry

/-- Gerver and Ramsey [GeRa79] (SOLVED; not proved here): in $\mathbb Z^2$ the answer is yes. -/
theorem erdos_problem_193.variants.gerver_ramsey_z2 :
    ∀ (S : Finset (Fin 2 → ℤ)) (a : ℕ → (Fin 2 → ℤ)),
      Function.Injective a →
      (∀ i, a (i + 1) - a i ∈ S) →
      ∃ i j k : ℕ, i < j ∧ j < k ∧
        ∃ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) ∧ ∀ c : Fin 2, x * (a j c - a i c) = y * (a k c - a i c) :=
  sorry

/-- Degenerate triples count as collinear (PROVED in Lean): `Collinear3 p q p` always holds. So the
statement needs three distinct points, which injectivity supplies. -/
theorem erdos_problem_193.collinear3_self_right (p q : Fin 3 → ℤ) : Collinear3 p q p :=
  ⟨0, 1, Or.inr one_ne_zero, fun k => by simp⟩

/-- Without injectivity the conclusion would be trivial for any walk that returns to a point two
steps later (PROVED in Lean). -/
theorem erdos_problem_193.variants.trivial_if_returns (a : ℕ → (Fin 3 → ℤ)) (h : a 2 = a 0) :
    ∃ i j k : ℕ, i < j ∧ j < k ∧ Collinear3 (a i) (a j) (a k) :=
  ⟨0, 1, 2, by norm_num, by norm_num, h ▸ erdos_problem_193.collinear3_self_right (a 0) (a 1)⟩
