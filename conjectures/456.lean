import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #456

Let $p_n$ be the smallest prime $\equiv 1 \pmod{n}$ and let $m_n$ be the
smallest positive integer such that $n \mid \phi(m_n)$.

1. Is it true that $m_n < p_n$ for almost all $n$?
2. Does $p_n / m_n \to \infty$ for almost all $n$?
3. Are there infinitely many primes $p$ such that $p - 1$ is the only $n$
   for which $m_n = p$?

Linnik's theorem implies that $p_n \leq n^{O(1)}$. It is trivial that
$m_n \leq p_n$ always. If $n = q - 1$ for some prime $q$ then $m_n = p_n$.
-/

/-- The smallest prime congruent to 1 modulo n. -/
noncomputable def smallestPrimeCong1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD n]}

/-- The smallest positive integer m such that n ∣ φ(m). -/
noncomputable def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ Nat.totient m}

/--
Erdős Problem #456, Part 1 [Er79e, p.80]:

Is it true that $m_n < p_n$ for almost all $n$?

Formalized as: the density of $\{n : m_n \geq p_n\}$ is 0, i.e., the
proportion of $n \leq x$ for which $p_n \leq m_n$ tends to 0 as $x \to \infty$.
-/
theorem erdos_problem_456_part1 :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        smallestPrimeCong1 n ≤ smallestTotientDiv n)).card : ℝ) / (x : ℝ))
      atTop (nhds 0) :=
  sorry

/--
Erdős Problem #456, Part 2 [Er79e, p.80]:

Does $p_n / m_n \to \infty$ for almost all $n$?

Formalized as: for every $C > 0$, the density of $\{n : p_n \leq C \cdot m_n\}$
is 0.
-/
theorem erdos_problem_456_part2 :
    ∀ C : ℝ, 0 < C →
      Tendsto (fun x : ℕ =>
        (((Finset.Icc 1 x).filter (fun n =>
          (smallestPrimeCong1 n : ℝ) ≤ C * (smallestTotientDiv n : ℝ))).card : ℝ) / (x : ℝ))
        atTop (nhds 0) :=
  sorry

/--
Erdős Problem #456, Part 3 [ErGr80, p.91]:

Are there infinitely many primes $p$ such that $p - 1$ is the only $n$ for
which $m_n = p$?
-/
theorem erdos_problem_456_part3 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      smallestTotientDiv (p - 1) = p ∧
      ∀ n : ℕ, smallestTotientDiv n = p → n = p - 1} :=
  sorry

end
