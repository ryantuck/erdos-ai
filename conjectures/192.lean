import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem #192

Let A = {a₁, a₂, …} ⊂ ℝ^d be an infinite sequence such that aᵢ₊₁ - aᵢ
is a positive unit vector (i.e. of the form (0,…,1,…,0)). For which d
must A contain a three-term arithmetic progression?

This is equivalent to the following question about abelian squares:
for which d does every infinite word over a d-letter alphabet contain
an abelian square (a pair of consecutive blocks that are permutations
of each other)?

Three points aᵢ, aⱼ, aₖ in such a sequence form a 3-term AP if and only
if j - i = k - j and the multiset of step directions from i to j equals
the multiset from j to k. This is precisely an abelian square in the
corresponding word of step directions.

The answer is: true for d ≤ 3, false for d ≥ 4.
- For d ≤ 3: any finite word of length ≥ 7 over 3 letters already
  contains an abelian square.
- For d ≥ 4: Keränen [Ke92] constructed an infinite word over 4 letters
  with no abelian square.
-/

/-- An infinite word `w : ℕ → α` contains an abelian square if there exist
    a starting position `i` and a block length `n ≥ 1` such that the multiset
    of characters in positions `i, …, i+n-1` equals the multiset of characters
    in positions `i+n, …, i+2n-1`. -/
def HasAbelianSquare {α : Type*} (w : ℕ → α) : Prop :=
  ∃ i n : ℕ, 0 < n ∧
    (Finset.range n).val.map (fun j => w (i + j)) =
    (Finset.range n).val.map (fun j => w (i + n + j))

/--
Erdős Problem #192, Part 1 [ErGr79, ErGr80]:
Every infinite word over a 3-letter alphabet contains an abelian square.
Equivalently, any infinite sequence in ℝ³ with unit-vector steps must
contain a three-term arithmetic progression.

In fact, any finite word of length ≥ 7 over {0,1,2} contains an abelian square.
-/
theorem erdos_problem_192_three_letters :
    ∀ w : ℕ → Fin 3, HasAbelianSquare w := by
  sorry

/--
Erdős Problem #192, Part 2 [ErGr79, ErGr80]:
There exists an infinite word over a 4-letter alphabet with no abelian square.
Equivalently, there exists an infinite sequence in ℝ⁴ with unit-vector steps
that contains no three-term arithmetic progression.

Proved by Keränen [Ke92].
-/
theorem erdos_problem_192_four_letters :
    ∃ w : ℕ → Fin 4, ¬HasAbelianSquare w := by
  sorry
