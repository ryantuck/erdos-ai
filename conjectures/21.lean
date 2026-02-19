import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

/--
A family of sets $\mathcal{F}$ is intersecting if any two sets in $\mathcal{F}$ have a non-empty intersection.
-/
def IsIntersecting (F : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

/--
The condition that any set $S$ with $|S| \le n-1$ is disjoint from at least one $A \in \mathcal{F}$.
This is equivalent to saying that there is no hitting set of size $\le n-1$.
-/
def HasNoSmallHittingSet (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ S : Finset ℕ, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

/--
A valid family for the problem is an intersecting family of sets of size $n$,
satisfying the "no small hitting set" condition.
-/
def IsValidFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  (∀ A ∈ F, A.card = n) ∧
  IsIntersecting F ∧
  HasNoSmallHittingSet n F

/--
Erdős-Lovász Conjecture (Problem #21):
Let $f(n)$ be the minimal size of an intersecting family of sets of size $n$
such that any set of size $n-1$ is disjoint from at least one member of the family.
The conjecture asks if $f(n) \ll n$.
Kahn (1994) proved that $f(n) \le C n$ for some constant $C$.
-/
theorem erdos_problem_21 :
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ∃ F : Finset (Finset ℕ), IsValidFamily n F ∧ (F.card : ℝ) ≤ C * (n : ℝ) :=
sorry
