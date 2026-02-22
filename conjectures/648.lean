import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Real

noncomputable section

/-!
# Erdős Problem #648

Let $g(n)$ denote the largest $t$ such that there exist integers
$2 \leq a_1 < a_2 < \cdots < a_t < n$ such that
$P(a_1) > P(a_2) > \cdots > P(a_t)$,
where $P(m)$ is the greatest prime factor of $m$. Estimate $g(n)$.

Stijn Cambie proved that $g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}$.
Cambie further asks whether there exists a constant $c$ such that
$g(n) \sim c \left(\frac{n}{\log n}\right)^{1/2}$, and shows that such $c$
must satisfy $2 \leq c \leq 2\sqrt{2}$.
-/

/-- The greatest prime factor of n, or 0 if n ≤ 1. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldr max 0

/-- g(n) is the largest t such that there exist integers 2 ≤ a₁ < a₂ < ··· < aₜ < n
    with P(a₁) > P(a₂) > ··· > P(aₜ), where P(m) is the greatest prime factor. -/
def erdos648_g (n : ℕ) : ℕ :=
  sSup {t : ℕ | ∃ a : Fin t → ℕ,
    (∀ i, 2 ≤ a i ∧ a i < n) ∧
    StrictMono a ∧
    StrictAnti (fun i => greatestPrimeFactor (a i))}

/--
Erdős Problem #648 (proved by Cambie [Ca25b]):

$g(n) \asymp \left(\frac{n}{\log n}\right)^{1/2}$, i.e., there exist positive
constants $c_1, c_2$ such that for all sufficiently large $n$,
$$c_1 \sqrt{\frac{n}{\log n}} \leq g(n) \leq c_2 \sqrt{\frac{n}{\log n}}.$$
-/
theorem erdos_problem_648 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c₁ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) ≤ (erdos648_g n : ℝ) ∧
      (erdos648_g n : ℝ) ≤ c₂ * Real.sqrt ((n : ℝ) / Real.log (n : ℝ)) :=
  sorry

end
