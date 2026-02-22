import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Finset Nat

/-!
# Erdős Problem #722 (PROVED)

Let k > r and n be sufficiently large in terms of k and r. Does there always
exist a Steiner system S(r, k, n), provided the trivial necessary divisibility
conditions C(k-i, r-i) | C(n-i, r-i) are satisfied for every 0 ≤ i < r?

That is, can one find a family of C(n,k)/C(k,r) many k-element subsets of
{1,...,n} such that every r-element subset is contained in exactly one set
in the family?

This was proved for (r,k) by:
- Kirkman for (2,3);
- Hanani [Ha61] for (3,4), (2,4), and (2,5);
- Wilson [Wi72] for (2,k) for any k;
- Keevash [Ke14] for all (r,k).
-/

/-- A Steiner system S(r, k, n): a collection F of k-element subsets of Fin n
    such that every r-element subset of Fin n is contained in exactly one
    member of F. -/
def IsSteinerSystem (r k n : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ F, B.card = k) ∧
  (∀ A : Finset (Fin n), A.card = r →
    ∃! B, B ∈ F ∧ A ⊆ B)

/-- The necessary divisibility conditions for a Steiner system S(r, k, n):
    for every 0 ≤ i < r, C(k-i, r-i) | C(n-i, r-i). -/
def SteinerDivisibilityConditions (r k n : ℕ) : Prop :=
  ∀ i < r, (Nat.choose (k - i) (r - i)) ∣ (Nat.choose (n - i) (r - i))

/--
Erdős Problem #722 (Keevash's theorem [Ke14]):

For every k > r ≥ 1, there exists N₀ such that for all n ≥ N₀, if the
necessary divisibility conditions are satisfied, then a Steiner system
S(r, k, n) exists.
-/
theorem erdos_problem_722 (r k : ℕ) (hr : r ≥ 1) (hkr : k > r) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      SteinerDivisibilityConditions r k n →
      ∃ F : Finset (Finset (Fin n)), IsSteinerSystem r k n F :=
  sorry
