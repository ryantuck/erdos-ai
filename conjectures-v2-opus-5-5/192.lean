-- [AI - Claude Opus 5.5]: Erdős Problem 192 — second-pass formalization
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #192

*Source:* [erdosproblems.com/192](https://www.erdosproblems.com/192) (status **SOLVED**: "This has
been resolved in some other way than a proof or disproof."; captured 2026-02-20). [ErGr79] [ErGr80]

Let $A=\{a_1,a_2,\ldots\}\subset \mathbb{R}^d$ be an infinite sequence such that $a_{i+1}-a_i$ is a
positive unit vector (i.e. is of the form $(0,0,\ldots,1,0,\ldots,0)$). For which $d$ must $A$
contain a three-term arithmetic progression?

Remarks recorded on the page (abridged): this is true for $d\leq 3$ and false for $d\geq 4$. The
problem is equivalent to one on 'abelian squares' (see [231]): $A$ is an infinite string over $d$
letters (the steps), and $p,q,r\in A$ form a three-term arithmetic progression if and only if the
steps from $p$ to $q$ are a permutation of the steps from $q$ to $r$. "It is easy to check that in
fact any finite string of length $7$ over $\{1,2,3\}$ contains an abelian square." An infinite
string without abelian squares was constructed when $d=4$ by Keränen [Ke92]. See the survey of
Fici and Puzynina [FiPu23].

## Encoding notes

* The two theorems state the answer in the abelian-square form: every ternary infinite word has
  an abelian square (so $d\le3$, and $d\le2$ by restriction), and some word over four letters has
  none (so $d\ge4$, and $d\ge5$ by inclusion). The equivalence with the original walks is the
  page's observation and is not formalized here; the original form is `variants.walk_statement`.
* **The page's remark is off by one, and the input's docstring repeats it.** The ternary word
  `cbcacbc` (here `2,1,2,0,2,1,2`) has length `7` and no abelian square
  (`variants.seven_letters_not_enough`, PROVED in Lean by `decide`). An exhaustive search (in the
  review) finds 118 abelian-square-free ternary words, the longest of length `7`; so every ternary
  word of length `8` contains an abelian square, and `8` is the correct threshold.

## References

From the site's `/latex/192` bibliography:
* [FiPu23] Fici, Gabriele and Puzynina, Svetlana, _Abelian combinatorics on words: a survey_.
  Comput. Sci. Rev. (2023), Paper No. 100532, 21.
* [Ke92] Keränen, Veikko, _Abelian squares are avoidable on 4 letters_. Automata, languages and
  programming (Vienna, 1992) (1992), 41–52.

Erdős's sources:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/192.lean` (Opus 5.5 review, `opus-5-5-review/192.md`).
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

In fact every finite ternary word of length at least 8 contains an abelian square; length 7 is not
enough (`variants.seven_letters_not_enough`). (Status: SOLVED; the true direction.)
-/
theorem erdos_problem_192_three_letters :
    ∀ w : ℕ → Fin 3, HasAbelianSquare w := by
  sorry

/--
Erdős Problem #192, Part 2 [ErGr79, ErGr80]:
There exists an infinite word over a 4-letter alphabet with no abelian square.
Equivalently, there exists an infinite sequence in ℝ⁴ with unit-vector steps
that contains no three-term arithmetic progression.

Proved by Keränen [Ke92]. (Status: SOLVED; the true direction.)
-/
theorem erdos_problem_192_four_letters :
    ∃ w : ℕ → Fin 4, ¬HasAbelianSquare w := by
  sorry

/-- The ternary word `2,1,2,0,2,1,2` (`cbcacbc`), continued by `0`s. -/
def word7_192 : ℕ → Fin 3 := fun j => ([2, 1, 2, 0, 2, 1, 2] : List (Fin 3)).getD j 0

/-- The page's remark (and the input's docstring) is off by one (PROVED in Lean by `decide`): the
word `cbcacbc` of length `7` has no abelian square inside its first seven letters. -/
theorem erdos_problem_192.variants.seven_letters_not_enough :
    ∀ i ∈ Finset.range 8, ∀ n ∈ Finset.range 8, 0 < n → i + 2 * n ≤ 7 →
      (Finset.range n).val.map (fun j => word7_192 (i + j)) ≠
        (Finset.range n).val.map (fun j => word7_192 (i + n + j)) := by
  decide

/-- The original form of the problem (SOLVED; not proved here): a walk in $\mathbb R^d$ with positive
unit steps must contain a three-term arithmetic progression exactly when $d\le3$. -/
theorem erdos_problem_192.variants.walk_statement :
    {d : ℕ | ∀ a : ℕ → Fin d → ℝ,
      (∀ n, ∃ i : Fin d, ∀ j, a (n + 1) j = a n j + if j = i then 1 else 0) →
      ∃ p q r : ℕ, p < q ∧ q < r ∧ ∀ j, a p j + a r j = 2 * a q j} = Set.Iic 3 :=
  sorry
