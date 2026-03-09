import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal Set

noncomputable section

/-!
# Erdős Problem #598

Let m be an infinite cardinal and κ be the successor cardinal of 2^ℵ₀.
Can one colour the countable subsets of m using κ many colours so that
every X ⊆ m with |X| = κ contains subsets of all possible colours?

Tags: set theory, ramsey theory
-/

/--
Erdős Problem #598 [Er87]:

Let m be an infinite cardinal and κ = (2^ℵ₀)⁺ (the successor of the continuum).
Can one colour the countable subsets of m using κ many colours so that every
subset X of cardinality κ contains countable subsets of every colour?

More precisely: for every infinite cardinal m and every type α with #α = m,
there exists a colouring c of the countable subsets of α with κ colours,
such that for every X ⊆ α with |X| = κ and every colour γ, some countable
subset of X receives colour γ.
-/
theorem erdos_problem_598 {α : Type} (hm : ℵ₀ ≤ #α) :
    let κ := Order.succ (2 ^ aleph 0)
    ∃ (Γ : Type) (_ : #Γ = κ) (c : {S : Set α // #S ≤ aleph 0} → Γ),
      ∀ (X : Set α), #X = κ →
        ∀ γ : Γ, ∃ S : {S : Set α // #S ≤ aleph 0},
          (S : Set α) ⊆ X ∧ c S = γ :=
  sorry

end
