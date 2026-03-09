import Mathlib.Data.Nat.Factorial.Basic

/--
Erdős Problem #398 [ErGr80]:

The Brocard-Ramanujan conjecture. Are the only solutions to
  n! = x² - 1
when n = 4, 5, 7?

That is, n! + 1 is a perfect square only for n = 4, 5, 7:
  4! + 1 = 25 = 5²
  5! + 1 = 121 = 11²
  7! + 1 = 5041 = 71²

Erdős and Graham describe this as an old conjecture and write it
"is almost certainly true but it is intractable at present".
Overholt (1993) showed it has only finitely many solutions assuming
a weak form of the ABC conjecture. No other solutions exist below 10⁹.
-/
theorem erdos_problem_398 :
    ∀ n x : ℕ, n.factorial + 1 = x ^ 2 → n = 4 ∨ n = 5 ∨ n = 7 :=
  sorry
