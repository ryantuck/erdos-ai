-- [AI-Generated]: Erdős Problem 1103 — second-pass formalization
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Classical

/-!
# Erdős Problem #1103

*Source:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
03 December 2025, captured 2026-02-23). [Er81h, p.180]

Let A = {a₀ < a₁ < a₂ < ⋯} be an infinite sequence of positive integers such that
every element of the sumset A + A is squarefree. How fast must A grow?

(The page says "infinite sequence of integers". Positivity is harmless: 0 ∉ A since
0 + 0 = 0 is not squarefree, and a strictly increasing integer sequence has only finitely
many negative terms, whose removal preserves the sumset condition and shifts indices by a
constant, which does not affect polynomial growth.)

Erdős notes there exists such a sequence which grows exponentially, but does not
expect such a sequence of polynomial growth to exist.

van Doorn and Tao [vDTa25] showed a_j > 0.24 j^{4/3} for all j, and that there
exists such a sequence (furthermore with squarefree terms) with a_j < exp(5j / log j)
for all large j (1-indexed). A superior lower bound a_j ≫ j^{15/11 - o(1)} had earlier
been found by Konyagin [Ko04] when considering the finite case (Problem #1109, the finite
analogue of this problem). van Doorn and Tao also obtain results for the generalisation
from squarefree to k-free integers, and for replacing A + A with A ∪ (A + A) ∪ (A + A + A).

In [Er81h] Erdős also asked whether there is an infinite sequence A such that, for every
a ∈ A and prime p, a ≡ t (mod p²) implies 1 ≤ t < p²/2 (such an A has A + A squarefree);
the page notes there are trivially at most finitely many such a, since there cannot be
any primes in (a^{1/2}, (2a)^{1/2}]. Not formalized here.

Tags: number theory. OEIS: A392164. The page records "Formalised statement? No" as of
capture.

## References

- [Er81h] Erdős, P., _Some problems and results on additive and multiplicative number
  theory_. Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.
- [Ko04] Konyagin, S. V., _Problems of the set of square-free numbers_. Izv. Ross. Akad.
  Nauk Ser. Mat. (2004), 63–90.
- [vDTa25] W. van Doorn and T. Tao, _Growth rates of sequences governed by the squarefree
  properties of its translates_. arXiv:2512.01087 (2025).

(All three as extracted by the original pipeline's fetch of `erdosproblems.com/latex/1103`;
volume numbers are not in that extraction. The glosses "Some applications of graph theory
and combinatorial methods to number theory and geometry" for [Er81h] and "van Doorn, F.
and Tao, T., Sumsets of squarefree numbers" for [vDTa25], carried by the archived styled
copy of this problem, are wrong.)
-/

/--
Erdős Problem #1103 [Er81h, p.180] (OPEN):

For any strictly increasing sequence a : ℕ → ℕ such that a(i) + a(j) is squarefree
for all i, j, the sequence does not have polynomial growth: for every C > 0 we have
a(j) > j^C for infinitely many j. This is Erdős's expectation ("does not expect such a
sequence of polynomial growth") read literally. It is the negation of
`∃ C, a(j) ≤ j^C for all large j`.

The first-pass file asserted the stronger "a(j) > j^C for *all sufficiently large* j".
That is a different, strictly stronger conjecture, because a sequence can outgrow every
polynomial along a subsequence while dipping below j² infinitely often. It is kept as
`erdos_problem_1103.variants.eventually_superpolynomial`.
-/
theorem erdos_problem_1103
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ C : ℝ, C > 0 →
      ∀ N : ℕ, ∃ j : ℕ, j ≥ N ∧
        (j : ℝ) ^ C < (a j : ℝ) :=
  sorry

/--
The stronger "eventual" form (OPEN, not stated on the source page): every such sequence
eventually outgrows every polynomial, i.e. for every C > 0, a(j) > j^C for all
sufficiently large j. It implies `erdos_problem_1103` but not conversely.
It would follow from the finite analogue (Problem #1109) with bound N^{o(1)}, since
`|A ∩ [1, x]|` is at most the finite maximum at every scale x.
-/
theorem erdos_problem_1103.variants.eventually_superpolynomial
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ C : ℝ, C > 0 →
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (j : ℝ) ^ C < (a j : ℝ) :=
  sorry

/--
van Doorn–Tao lower bound [vDTa25] (solved): a_j > 0.24 j^{4/3} for all j, in the
source's 1-indexing. With 0-indexing `a j` is the source's a_{j+1}, hence the `j + 1`.
-/
theorem erdos_problem_1103.variants.vDTa25_lower
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ j : ℕ, (24 / 100 : ℝ) * ((j : ℝ) + 1) ^ ((4 : ℝ) / 3) < (a j : ℝ) :=
  sorry

/--
Konyagin's lower bound [Ko04] (solved, via the finite case #1109): a_j ≫ j^{15/11 - o(1)},
i.e. for every ε > 0, a_j > j^{15/11 - ε} for all sufficiently large j.
-/
theorem erdos_problem_1103.variants.konyagin_lower
    (a : ℕ → ℕ)
    (ha_strict_mono : StrictMono a)
    (ha_sumset_sqfree : ∀ i j : ℕ, Squarefree (a i + a j)) :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (j : ℝ) ^ ((15 : ℝ) / 11 - ε) < (a j : ℝ) :=
  sorry

/--
van Doorn–Tao construction [vDTa25] (solved): there is such a sequence, with squarefree
terms, satisfying a_j < exp(5j / log j) for all large j (1-indexed; `a j` is the source's
a_{j+1}, hence the `j + 1`).
-/
theorem erdos_problem_1103.variants.vDTa25_upper :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i j : ℕ, Squarefree (a i + a j)) ∧
      (∀ j : ℕ, Squarefree (a j)) ∧
      ∃ N : ℕ, ∀ j : ℕ, j ≥ N →
        (a j : ℝ) < Real.exp (5 * ((j : ℝ) + 1) / Real.log ((j : ℝ) + 1)) :=
  sorry

end
