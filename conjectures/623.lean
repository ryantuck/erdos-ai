import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Data.Finset.Basic

open Cardinal Ordinal

/--
Erdős Problem #623 [ErHa58, Er99]:

A problem of Erdős and Hajnal. Let X be a set of cardinality ℵ_ω and f be a
function from the finite subsets of X to X such that f(A) ∉ A for all A. Must
there exist an infinite Y ⊆ X that is independent — that is, for all finite
B ⊂ Y we have f(B) ∉ Y?

Erdős and Hajnal proved that if |X| < ℵ_ω then the answer is no. Erdős
suggested in [Er99] that this problem is "perhaps undecidable".
-/
theorem erdos_problem_623
    (X : Type*) (hX : #X = ℵ_ ω)
    (f : Finset X → X) (hf : ∀ A : Finset X, f A ∉ A) :
    ∃ Y : Set X, Set.Infinite Y ∧
      ∀ B : Finset X, (↑B : Set X) ⊆ Y → f B ∉ Y :=
  sorry
