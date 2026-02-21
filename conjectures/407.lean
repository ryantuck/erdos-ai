import Mathlib.Data.Finset.Card

/-!
# Erdős Problem #407

Let w(n) count the number of solutions to n = 2^a + 3^b + 2^c · 3^d with
a, b, c, d ≥ 0 integers. Is it true that w(n) is bounded by some absolute
constant?

A conjecture originally due to Newman. This was proved by Evertse, Györy,
Stewart, and Tijdeman [EGST88]. Bajpai and Bennett [BaBe24] showed that
w(n) ≤ 4 for n ≥ 131082 and w(n) ≤ 9 for all n.
-/

/--
Erdős Problem #407 [ErGr80, p.80]:

There exists an absolute constant C such that for every natural number n,
the number of 4-tuples (a, b, c, d) of natural numbers satisfying
n = 2^a + 3^b + 2^c · 3^d is at most C.
-/
theorem erdos_problem_407 :
    ∃ C : ℕ, ∀ (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)),
      (∀ t ∈ S, n = 2 ^ t.1 + 3 ^ t.2.1 + 2 ^ t.2.2.1 * 3 ^ t.2.2.2) →
      S.card ≤ C :=
  sorry
