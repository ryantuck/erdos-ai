import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Classical Filter BigOperators Finset

noncomputable section

/-!
# Erdős Problem #298

Does every set A ⊆ ℕ of positive density contain some finite S ⊂ A such that
∑_{n ∈ S} 1/n = 1?

A problem of Erdős and Graham [ErGr80, Er92c]. The answer is yes, proved by
Bloom [Bl21].

Tags: number theory | unit fractions
-/

/-- The upper density of a set A ⊆ ℕ, defined as
    limsup_{N → ∞} |A ∩ {0, ..., N-1}| / N. -/
noncomputable def Nat.upperDensity298 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ =>
    ((Finset.filter (· ∈ A) (Finset.range N)).card : ℝ) / N) atTop

/--
**Erdős Problem #298** [ErGr80, Er92c]:

If A ⊆ ℕ has positive upper density, then there exists a finite nonempty
subset S ⊆ A such that ∑_{n ∈ S} 1/n = 1.

Proved by Bloom [Bl21].
-/
theorem erdos_problem_298 (A : Set ℕ) (hA : Nat.upperDensity298 A > 0) :
    ∃ S : Finset ℕ, S.Nonempty ∧ (∀ n ∈ S, n ∈ A ∧ 0 < n) ∧
      (∑ n ∈ S, (1 : ℚ) / n) = 1 :=
  sorry

end
