-- [AI-Generated]: Erdős Problem 1108 — second-pass formalization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset

noncomputable section

/-!
# Erdős Problem #1108

*Source:* [erdosproblems.com/1108](https://www.erdosproblems.com/1108) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
04 November 2025, captured 2026-03-09). [Ob1]

Let A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }. If k ≥ 2, does A contain only
finitely many k-th powers? Does it contain only finitely many powerful numbers?

Asked by Erdős at Oberwolfach in 1988 [Ob1]. It is open even whether there are
infinitely many squares of the form 1 + n! (see problem #398).

This was motivated in part by a problem of Mahler, which he discussed with Erdős a few
days before his death in 1988. If k ≥ 5 and A_k = { ∑_{n ∈ S} kⁿ : S ⊂ ℕ finite }, does A_k
contain only finitely many squares? Mahler showed there are infinitely many squares in
A_k for k ≤ 4, and found only one square for k ≥ 5, namely 1 + 7 + 7² + 7³ = 400. (That
example uses 7⁰ = 1, so the page's ℕ contains 0.) Brindza and Erdős [BrEr91] proved that,
for any r, if n₁! + ⋯ + nᵣ! is powerful then n₁ ≪_r 1. That result is not formalized here,
because the page does not fix the ordering of the nᵢ.

## Encoding notes

* S ranges over finite subsets of ℕ including 0, following the page's own convention (see
  the Mahler example). So 0! and 1! are both available: A contains 4 = 0! + 1! + 2!,
  10 and 28, which are not sums of *distinct factorial values*. Under that alternative
  reading A would be a subset, and both theorems below would be slightly stronger than
  needed. Below 16! the only square or powerful number this adds is 4.
* The powerful-number statement implies the k-th-power statement, since every b^k with
  b ≥ 1 and k ≥ 2 is powerful and b = 0 contributes only one element.
* Computation (review scratch script, S ⊆ {0, …, 16}, complete below 16!). The squares in
  A are 0, 1, 4, 9, 25, 121, 144, 729, 841, 5041, 5184, 45369, 46225, 363609, 403225,
  3674889 and 1401602635449, and the cubes are 0, 1, 8, 27, 729. There are 27 powerful
  numbers, the largest being 1401602635449.

Tags: number theory, factorials. OEIS: A051761, A115645, A025494. The page records an
upstream formalised statement.

## References

* [Ob1] P. Erdős, _Oberwolfach Mathematical Problems, Volume 1_. Mathematisches
  Forschungsinstitut Oberwolfach (problem posed 1988).
* [BrEr91] Brindza, B. and Erdős, P., _On some Diophantine problems involving powers and
  factorials_. J. Austral. Math. Soc. Ser. A 51 (1991), 1–7.

(Provenance: [Ob1] from the original pipeline's fetch of `erdosproblems.com/latex/854`,
which cites the same key. [BrEr91] from the sibling file `deepmind/deepmind/405.lean` in
this repository, which cites the same key; that entry is model-written and not
`/latex`-verified.)
-/

/-- The set A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite }, i.e. sums of factorials of *distinct
indices* n. Since 0 ∈ ℕ, both 0! = 1 and 1! = 1 are available (see the module docstring). -/
def IsFactorialSubsetSum1108 (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial

/-- A positive natural number n is **powerful** if for every prime p dividing n,
    we have p² ∣ n. -/
def IsPowerful1108 (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/--
Erdős Problem #1108, part 1 [Ob1] (OPEN):

If k ≥ 2, then A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contains only finitely
many k-th powers.

Stated in the asked ("yes") direction as a direct assertion (this raw corpus has no
`answer()` elaborator). It follows from part 2.
-/
theorem erdos_problem_1108a (k : ℕ) (hk : 2 ≤ k) :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ ∃ b : ℕ, m = b ^ k} :=
  sorry

/--
Erdős Problem #1108, part 2 [Ob1] (OPEN):

A = { ∑_{n ∈ S} n! : S ⊂ ℕ finite } contains only finitely many powerful
numbers.

Stated in the asked ("yes") direction as a direct assertion.
-/
theorem erdos_problem_1108b :
    Set.Finite {m : ℕ | IsFactorialSubsetSum1108 m ∧ IsPowerful1108 m} :=
  sorry

/-- Mahler's motivating question (OPEN; a related problem, not part of #1108): for k ≥ 5,
A_k = { ∑_{n ∈ S} kⁿ : S ⊂ ℕ finite } contains only finitely many squares. It is stated in
the asked direction. The only square Mahler found is 400 = 7⁰ + 7¹ + 7² + 7³. -/
theorem erdos_problem_1108.variants.mahler :
    ∀ k : ℕ, 5 ≤ k →
      Set.Finite {m : ℕ | (∃ S : Finset ℕ, m = ∑ n ∈ S, k ^ n) ∧ ∃ b : ℕ, m = b ^ 2} :=
  sorry

/-- Mahler (solved; related problem): for 2 ≤ k ≤ 4, A_k contains infinitely many squares.
The case k = 2 is trivial, since A_2 = ℕ. -/
theorem erdos_problem_1108.variants.mahler_small :
    ∀ k : ℕ, 2 ≤ k → k ≤ 4 →
      Set.Infinite {m : ℕ | (∃ S : Finset ℕ, m = ∑ n ∈ S, k ^ n) ∧ ∃ b : ℕ, m = b ^ 2} :=
  sorry

end
