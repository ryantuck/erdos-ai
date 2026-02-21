import Mathlib.Data.Fin.Basic

/-!
# Erdős Problem #231

Let S be a string of length 2^k - 1 formed from an alphabet of k characters.
Must S contain an abelian square: two consecutive blocks x and y such that
y is a permutation of x?

Erdős initially conjectured the answer is yes for all k ≥ 2, but this was
disproved for k ≥ 4. Keränen [Ke92] constructed an infinite word over
{1,2,3,4} with no abelian square, giving a negative answer for all k ≥ 4.

The answer is:
- Yes for k ≤ 3 (any word of length ≥ 7 over 3 letters contains an
  abelian square)
- No for k ≥ 4
-/

/-- A list contains an abelian square if there exist two consecutive blocks of
    equal positive length that are permutations of each other. -/
def ContainsAbelianSquare {α : Type*} (w : List α) : Prop :=
  ∃ i n : ℕ, 0 < n ∧ i + 2 * n ≤ w.length ∧
    List.Perm ((w.drop i).take n) ((w.drop (i + n)).take n)

/--
Erdős Problem #231, Part 1:
For k ≤ 3 (with k ≥ 2), every string of length 2^k - 1 over k characters
contains an abelian square.
-/
theorem erdos_problem_231_small_alphabet (k : ℕ) (hk : 2 ≤ k) (hk3 : k ≤ 3)
    (w : List (Fin k)) (hw : w.length = 2 ^ k - 1) :
    ContainsAbelianSquare w := by
  sorry

/--
Erdős Problem #231, Part 2 (Disproved):
For k ≥ 4, there exists a string of length 2^k - 1 over k characters with
no abelian square, disproving the original conjecture.
-/
theorem erdos_problem_231_disproved (k : ℕ) (hk : 4 ≤ k) :
    ∃ w : List (Fin k), w.length = 2 ^ k - 1 ∧ ¬ContainsAbelianSquare w := by
  sorry
