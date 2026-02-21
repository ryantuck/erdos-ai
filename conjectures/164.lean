import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Real

noncomputable section

/-!
# Erdős Problem #164

A set A ⊂ ℕ is primitive if no member of A divides another. Is the sum
∑_{n ∈ A} 1/(n log n) maximised over all primitive sets when A is the set of
primes?

Erdős [Er35] proved that this sum always converges for a primitive set.
Lichtman [Li23] proved that the answer is yes.
-/

/-- A set A of natural numbers is primitive (an antichain under divisibility)
    if no element divides a distinct element: for all a, b ∈ A, a ∣ b → a = b. -/
def IsPrimitive (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/--
Erdős Conjecture (Problem #164) [Er76g, Er86]:

For any primitive set A ⊆ {2, 3, 4, ...} of natural numbers,
  ∑_{n ∈ A} 1/(n · log n) ≤ ∑_{p prime} 1/(p · log p).

That is, the sum ∑ 1/(n log n) over any primitive set is maximised when
the set is the set of all primes.

Proved by Lichtman [Li23].
-/
theorem erdos_problem_164 :
    ∀ A : Set ℕ, IsPrimitive A → A ⊆ {n : ℕ | 2 ≤ n} →
    ∑' n : A, (1 : ℝ) / (((n : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ)) ≤
    ∑' p : {p : ℕ | Nat.Prime p}, (1 : ℝ) / (((p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)) :=
  sorry

end
