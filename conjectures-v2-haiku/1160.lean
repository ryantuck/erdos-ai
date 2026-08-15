import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section
open Classical

namespace Erdos1160

/-- Two group structures on the same type are isomorphic if there exists
    a multiplicative equivalence between them. -/
def GroupStructIso (n : ℕ) (G₁ G₂ : Group (Fin n)) : Prop :=
  Nonempty (@MulEquiv (Fin n) (Fin n) G₁.toMul G₂.toMul)

/-- Group isomorphism is an equivalence relation on group structures on Fin n. -/
instance groupStructSetoid (n : ℕ) : Setoid (Group (Fin n)) where
  r := GroupStructIso n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨@MulEquiv.refl (Fin n) G.toMul⟩
    · intro G₁ G₂ ⟨e⟩
      exact ⟨@MulEquiv.symm (Fin n) (Fin n) G₁.toMul G₂.toMul e⟩
    · intro G₁ G₂ G₃ ⟨e₁⟩ ⟨e₂⟩
      exact ⟨@MulEquiv.trans (Fin n) (Fin n) (Fin n) G₁.toMul G₂.toMul G₃.toMul e₁ e₂⟩

/-- The number of isomorphism classes of groups of order n (OEIS A000001).
    Defined as the cardinality of group structures on Fin n modulo isomorphism.

    Note: This definition uses Nat.card on the quotient type, which returns 0 for
    non-Finite types. Mathematically, the quotient is finite for all n (there are
    finitely many group structures on a finite set), but this finiteness is not
    explicitly asserted in the current formalization. A complete formal development
    would require establishing Finite (Quotient (groupStructSetoid n)) as a separate
    lemma before applying Nat.card. -/
noncomputable def numGroupsOfOrder (n : ℕ) : ℕ :=
  Nat.card (Quotient (groupStructSetoid n))

/--
Erdős Problem #1160 [Va99, 5.71]:

Let g(n) denote the number of groups of order n. If n ≤ 2^m then g(n) ≤ g(2^m).

This conjecture states that among all n ≤ 2^m, the value g(n) is maximized
at n = 2^m (i.e., powers of 2 have the most groups of any order up to that
point). Listed as Question 22.16 in [BNV07], attributed to Erdős and Higman.

Partial result [Pa03]: The conjecture has been verified for all odd n when m ≥ 3619.

Bibliography:
- [Va99] Vaughan, 1999, section 5.71 (reference details pending)
- [BNV07] Blackburn, Neumann, Venkataraman, 2007, Question 22.16
- [Pa03] Pantelidakis, 2003 (proved conjecture for odd n when m ≥ 3619)

Tags: group theory
-/
theorem erdos_problem_1160 (n m : ℕ) (h : n ≤ 2 ^ m) :
    numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) :=
  sorry

end Erdos1160

end
