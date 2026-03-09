import Mathlib.Data.Set.Function
import Mathlib.Order.Disjoint

open Set Function

/--
A sequence f : ℕ → ℕ contains a **monotone 3-term arithmetic progression** if
there exist indices i < j < k such that f(i) < f(j) < f(k) and they form an
arithmetic progression, i.e., f(j) - f(i) = f(k) - f(j).
-/
def HasMonotone3TermAP (f : ℕ → ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧
    f i < f j ∧ f j < f k ∧
    f j - f i = f k - f j

/--
A set S ⊆ ℕ **can be permuted to avoid monotone 3-term APs** if there exists
an injective enumeration of S (a bijection ℕ → S) whose induced sequence
contains no monotone 3-term arithmetic progression.
-/
def CanPermuteToAvoidMonotone3AP (S : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, range f = S ∧ Injective f ∧ ¬HasMonotone3TermAP f

/--
Erdős Problem #197 [ErGr79, ErGr80]:

Can ℕ be partitioned into two sets, each of which can be permuted to avoid
monotone 3-term arithmetic progressions?

If three sets are allowed then this is possible.
-/
theorem erdos_problem_197 :
    ∃ (A B : Set ℕ), A ∪ B = univ ∧ Disjoint A B ∧
      CanPermuteToAvoidMonotone3AP A ∧ CanPermuteToAvoidMonotone3AP B :=
  sorry
