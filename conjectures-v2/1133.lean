import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card

open Polynomial Finset Set

noncomputable section

namespace Erdos1133

/-!
# Erdős Problem #1133

Let C > 0. There exists ε > 0 such that if n is sufficiently large the following holds.

For any x₁, ..., xₙ ∈ [-1,1] there exist y₁, ..., yₙ ∈ [-1,1] such that, if P is a
polynomial of degree m < (1+ε)n with P(xᵢ) = yᵢ for at least (1-ε)n many 1 ≤ i ≤ n,
then max_{x ∈ [-1,1]} |P(x)| > C.

Erdős proved that, for any C > 0, there exists ε > 0 such that if n is sufficiently
large and m = ⌊(1+ε)n⌋ then for any x₁, ..., xₘ ∈ [-1,1] there is a polynomial P of
degree n such that |P(xᵢ)| ≤ 1 for 1 ≤ i ≤ m and max_{x ∈ [-1,1]} |P(x)| > C.
The conjectured statement would also imply this, but Erdős in [Er67] says he could
not even prove it for m = n.

Status on erdosproblems.com/1133: OPEN ("This is open, and cannot be resolved with a
finite computation.") — page last edited 31 December 2025, accessed 2026-02-23.
Source citation on the page: [Er67, p.72]. Tags: analysis | polynomials. No OEIS
entry and no cross-referenced problems on the page.

Reference ([Er67] recovered from the original pipeline's fetch of
erdosproblems.com/latex/1133 preserved in the session logs; the volume number was
absent from the recovered extraction and is deliberately not invented):

- [Er67] Erdős, P., _Problems and results on the convergence and divergence
  properties of the Lagrange interpolation polynomials and some extremal problems_.
  Mathematica (Cluj) (1967), 65–73. This problem: p. 72.

NOTE: the main statement below is unchanged from the input file (the Fable review of
2026-08-14 found no semantic defects); the citation data and the page-confirmed
variant were added by that review and are not compile-verified (the review container
cannot run `lake build`).
-/

/--
Erdős Problem #1133 [Er67, p.72], OPEN:

Let C > 0. There exists ε > 0 such that for sufficiently large n, for any
x₁, ..., xₙ ∈ [-1,1] there exist y₁, ..., yₙ ∈ [-1,1] such that any polynomial P
of degree < (1+ε)n that agrees with yᵢ at xᵢ for at least (1-ε)n indices i
must satisfy max_{x ∈ [-1,1]} |P(x)| > C.
-/
theorem erdos_problem_1133 :
    ∀ C : ℝ, C > 0 →
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ x : Fin n → ℝ, (∀ i, x i ∈ Icc (-1 : ℝ) 1) →
    ∃ y : Fin n → ℝ, (∀ i, y i ∈ Icc (-1 : ℝ) 1) ∧
    ∀ P : Polynomial ℝ, (P.natDegree : ℝ) < (1 + ε) * n →
    ((univ.filter (fun i : Fin n => P.eval (x i) = y i)).card : ℝ) ≥ (1 - ε) * n →
    ∃ t ∈ Icc (-1 : ℝ) 1, |P.eval t| > C :=
  sorry

/--
Variant (page remark, SOLVED by Erdős [Er67]): for any C > 0 there exists ε > 0 such
that if n is sufficiently large and m = ⌊(1+ε)n⌋ then for any x₁, ..., xₘ ∈ [-1,1]
there is a polynomial P of degree n with |P(xᵢ)| ≤ 1 for 1 ≤ i ≤ m and
max_{x ∈ [-1,1]} |P(x)| > C.

Encoding notes: the fixed node count m = ⌊(1+ε)n⌋ is stated here as "for every
m ≤ (1+ε)n" (over ℝ, avoiding `Nat.floor`), which is equivalent: taking
m = ⌊(1+ε)n⌋ recovers the page's statement, and conversely a node family of size
m ≤ ⌊(1+ε)n⌋ can be padded (repeating one node, or the node 0 when m = 0) to size
exactly ⌊(1+ε)n⌋, and the polynomial obtained for the padded family works for the
original one. "Degree n" is taken literally as `P.natDegree = n`, and the maximum
over the compact interval is encoded by an existential witness, which is exact
(the maximum exceeds C iff some point does).

NOTE: added by the Fable review of 2026-08-14 from the recovered source page; not
compile-verified.
-/
theorem erdos_problem_1133.variants.erdos_bounded_at_nodes :
    ∀ C : ℝ, C > 0 →
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ m : ℕ, (m : ℝ) ≤ (1 + ε) * n →
    ∀ x : Fin m → ℝ, (∀ i, x i ∈ Icc (-1 : ℝ) 1) →
    ∃ P : Polynomial ℝ, P.natDegree = n ∧
      (∀ i, |P.eval (x i)| ≤ 1) ∧
      ∃ t ∈ Icc (-1 : ℝ) 1, |P.eval t| > C :=
  sorry

end Erdos1133
