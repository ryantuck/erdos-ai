import Mathlib.Data.Nat.Totient
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set

noncomputable section

/-!
# Erdős Problem #821

Let $g(n)$ count the number of $m$ such that $\phi(m) = n$. Is it true that,
for every $\epsilon > 0$, there exist infinitely many $n$ such that
$g(n) > n^{1 - \epsilon}$?

Pillai proved that $\limsup g(n) = \infty$ and Erdős [Er35b] proved that there
exists some constant $c > 0$ such that $g(n) > n^c$ for infinitely many $n$.
The best known bound is $g(n) > n^{0.71568...}$ for infinitely many $n$,
obtained by Lichtman [Li22].
-/

/-- The number of positive integers m such that φ(m) = n. -/
noncomputable def totientPreimageCount (n : ℕ) : ℕ :=
  Nat.card {m : ℕ // 0 < m ∧ Nat.totient m = n}

/--
Erdős Problem #821 [Er74b]:

For every ε > 0, there exist infinitely many n such that g(n) > n^{1-ε},
where g(n) counts the number of m with φ(m) = n.
-/
theorem erdos_problem_821 :
    ∀ ε : ℝ, ε > 0 →
      Set.Infinite {n : ℕ | (totientPreimageCount n : ℝ) > (n : ℝ) ^ (1 - ε)} :=
  sorry

end
