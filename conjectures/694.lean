import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic

open Nat

noncomputable section

/--
Erdős Problem #694 [Er79e]:

Let $f_{\max}(n)$ be the largest $m$ such that $\phi(m)=n$, and $f_{\min}(n)$ be
the smallest such $m$, where $\phi$ is Euler's totient function. Investigate
$$\max_{n \le x} \frac{f_{\max}(n)}{f_{\min}(n)}.$$

We formalize this as the conjecture that the ratio $f_{\max}(n)/f_{\min}(n)$
is unbounded: for any constant $C > 0$, there exist $m_1, m_2$ with
$\phi(m_1) = \phi(m_2)$ and $m_1 / m_2 \ge C$.

See also Problem #51.
-/
theorem erdos_problem_694 :
    ∀ C : ℝ, C > 0 →
      ∃ a m₁ m₂ : ℕ, m₂ ≠ 0 ∧
        Nat.totient m₁ = a ∧ Nat.totient m₂ = a ∧
        (↑m₁ : ℝ) / (↑m₂ : ℝ) ≥ C :=
  sorry
