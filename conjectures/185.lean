import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi

noncomputable section

/-!
# Erdős Problem #185

Let f₃(n) be the maximal size of a subset of {0,1,2}^n which contains no three
points on a line. Is it true that f₃(n) = o(3^n)?

Originally considered by Moser. It is trivial that f₃(n) ≥ R₃(3^n), the maximal
size of a subset of {1,…,3^n} without a three-term arithmetic progression.
Moser showed that f₃(n) ≫ 3^n / √n. The answer is yes, which is a corollary of
the density Hales-Jewett theorem, proved by Furstenberg and Katznelson [FuKa91].
-/

/-- A combinatorial line in {0,1,2}^n consists of three points parameterized by
j ∈ {0,1,2}, such that there exists a nonempty set S of "active" coordinates
where the j-th point has value j at each active coordinate, and all three points
agree at non-active coordinates. -/
def IsCombinatorialLine (n : ℕ) (p : Fin 3 → (Fin n → Fin 3)) : Prop :=
  ∃ (S : Finset (Fin n)), S.Nonempty ∧
    ∃ (c : Fin n → Fin 3),
      ∀ (j : Fin 3) (i : Fin n),
        p j i = if i ∈ S then j else c i

/--
Erdős Problem #185 (Density Hales-Jewett for k=3) [Er73]:

For every ε > 0, there exists N such that for all n ≥ N, every subset A ⊆ {0,1,2}^n
of size |A| > ε · 3^n contains a combinatorial line (three points on a line).

Equivalently, the maximum size f₃(n) of a line-free subset of {0,1,2}^n satisfies
f₃(n) = o(3^n).
-/
theorem erdos_problem_185 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ A : Finset (Fin n → Fin 3),
          (A.card : ℝ) > ε * (3 : ℝ) ^ n →
          ∃ p : Fin 3 → (Fin n → Fin 3),
            IsCombinatorialLine n p ∧ ∀ j : Fin 3, p j ∈ A :=
  sorry

end
