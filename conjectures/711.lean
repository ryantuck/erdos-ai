import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #711

Let f(n,m) be minimal such that in (m, m+f(n,m)) there exist distinct integers
a₁, …, aₙ such that k ∣ aₖ for all 1 ≤ k ≤ n. Prove that
  max_m f(n,m) ≤ n^{1+o(1)}
and that
  max_m (f(n,m) - f(n,n)) → ∞.

A problem of Erdős and Pomerance [ErPo80], who proved that
  max_m f(n,m) ≪ n^{3/2}
and
  n(log n / log log n)^{1/2} ≪ f(n,n) ≪ n(log n)^{1/2}.

van Doorn [vD26] proved the second part, showing that for all large n
there exists m with f(n,m) - f(n,n) ≫ (log n / log log n) · n.

See also [710].

https://www.erdosproblems.com/711
-/

/-- f(n,m) for Erdős Problem #711: the minimal f such that in the open interval
    (m, m+f) there exist n distinct integers a₁, ..., aₙ with k ∣ aₖ for all
    1 ≤ k ≤ n. When m = n this coincides with the function in Problem #710. -/
noncomputable def erdos711_f (n m : ℕ) : ℕ :=
  sInf {f : ℕ | ∃ g : Fin n → ℕ,
    Function.Injective g ∧
    (∀ i : Fin n, m < g i) ∧
    (∀ i : Fin n, g i < m + f) ∧
    (∀ i : Fin n, (i.val + 1) ∣ g i)}

/--
Erdős Problem #711, Part 1 [ErPo80]:

Prove that max_m f(n,m) ≤ n^{1+o(1)}.

Formulated as: for every ε > 0, there exists N₀ such that for all n ≥ N₀
and all m,
  f(n,m) ≤ n^{1+ε}.

Erdős and Pomerance proved the weaker bound max_m f(n,m) ≪ n^{3/2}.
-/
theorem erdos_problem_711_part1 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ m : ℕ,
        (erdos711_f n m : ℝ) ≤ (n : ℝ) ^ (1 + ε) :=
  sorry

/--
Erdős Problem #711, Part 2 [ErPo80]:

Prove that max_m (f(n,m) - f(n,n)) → ∞.

Formulated as: for every C, there exists N₀ such that for all n ≥ N₀,
there exists m with f(n,m) ≥ f(n,n) + C.

van Doorn [vD26] proved that for all large n there exists m with
  f(n,m) - f(n,n) ≫ (log n / log log n) · n.
-/
theorem erdos_problem_711_part2 :
    ∀ C : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ m : ℕ, erdos711_f n m ≥ erdos711_f n n + C :=
  sorry

end
