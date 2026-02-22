import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

noncomputable section

/-!
# Erdős Problem #970

Let h(k) be Jacobsthal's function, defined as the minimal m such that,
if n has at most k prime factors, then in any set of m consecutive
integers there exists an integer coprime to n. Is it true that h(k) ≪ k²?

This is Jacobsthal's conjecture. Iwaniec [Iw78] proved h(k) ≪ (k log k)².
The best known lower bound is h(k) ≫ k · (log k)(log log log k)/(log log k)²,
due to Ford, Green, Konyagin, Maynard, and Tao [FGKMT18].

This is a more general form of the function considered in problem 687.
-/

/-- Jacobsthal's function h(k): the smallest m such that for every positive
    integer n with at most k distinct prime factors, among any m consecutive
    natural numbers there is one coprime to n. -/
noncomputable def jacobsthal (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ n : ℕ, 0 < n → n.primeFactors.card ≤ k →
    ∀ a : ℕ, ∃ i : ℕ, i < m ∧ Nat.Coprime (a + i) n}

/--
Erdős Problem #970 (Jacobsthal's conjecture) [Er65b]:

h(k) ≪ k², i.e., there exists a constant C > 0 such that h(k) ≤ C · k²
for all k.
-/
theorem erdos_problem_970 :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, (jacobsthal k : ℝ) ≤ C * (k : ℝ) ^ 2 :=
  sorry

end
