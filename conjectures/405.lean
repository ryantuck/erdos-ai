import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #405

Let p be an odd prime. Is it true that the equation
  (p-1)! + a^{p-1} = p^k
has only finitely many solutions?

Erdős and Graham remark that it is probably true that in general
(p-1)! + a^{p-1} is rarely a power at all (although this can happen,
for example 6! + 2⁶ = 28²).

Brindza and Erdős [BrEr91] proved that there are finitely many solutions.
Yu and Liu [YuLi96] showed that the only solutions are
  2! + 1² = 3,  2! + 5² = 3³,  and  4! + 1⁴ = 5².
-/

/--
Erdős Problem #405 [ErGr80, p.80]:

There are only finitely many triples (p, a, k) of natural numbers with p an
odd prime such that (p-1)! + a^{p-1} = p^k.
-/
theorem erdos_problem_405 :
    Set.Finite {t : ℕ × ℕ × ℕ |
      let p := t.1
      let a := t.2.1
      let k := t.2.2
      Nat.Prime p ∧ p ≠ 2 ∧ (p - 1).factorial + a ^ (p - 1) = p ^ k} :=
  sorry
