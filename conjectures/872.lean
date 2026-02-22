import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Classical

noncomputable section

/-!
# Erdős Problem #872

Consider the two-player game in which players alternately choose integers
from {2, 3, …, n} to be included in some set A such that no a ∣ b for
a ≠ b ∈ A (i.e., A remains a primitive set — an antichain under divisibility).
The game ends when no legal move is possible.

One player (the Lengthener) wants the game to last as long as possible;
the other (the Shortener) wants it to end quickly.

At least εn moves (for some ε > 0 and n sufficiently large)?
At least (1 − ε)n/2 moves (for any ε > 0 and n sufficiently large)?

Erdős does not specify which player goes first, which may affect the answer.
This is a type of saturation game.
-/

/-- A finset of natural numbers is *primitive* (an antichain under divisibility)
    if a ∣ b with a, b ∈ A implies a = b. -/
def IsPrimitive872 (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b

/-- The universe of moves in the game: {2, 3, …, n}. -/
def gameUniverse872 (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (· ≥ 2)

/-- Legal moves from a primitive position A ⊆ {2,…,n}: elements x in the
    universe not in A such that inserting x keeps the set primitive. -/
noncomputable def legalMoves872 (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (gameUniverse872 n \ A).filter fun x =>
    ∀ a ∈ A, ¬(a ∣ x) ∧ ¬(x ∣ a)

/-- A legal strategy for the primitive-set game on {2,…,n}: given any
    game state with at least one legal move, it picks a legal move. -/
def LegalStrategy872 (n : ℕ) :=
  (A : Finset ℕ) → (legalMoves872 n A).Nonempty → {x // x ∈ legalMoves872 n A}

/-- Play the game with given legal strategies for the Lengthener and Shortener.
    `lengthenerTurn = true` means it is the Lengthener's turn.
    The `fuel` parameter bounds recursion depth (n + 1 suffices).
    Returns the total number of moves played. -/
noncomputable def playGame872 (n : ℕ) (sL sS : LegalStrategy872 n) :
    ℕ → Finset ℕ → Bool → ℕ
  | 0, _, _ => 0
  | fuel + 1, A, lengthenerTurn =>
    if h : (legalMoves872 n A).Nonempty then
      let strategy := if lengthenerTurn then sL else sS
      let x := (strategy A h).val
      1 + playGame872 n sL sS fuel (insert x A) (!lengthenerTurn)
    else 0

/--
Erdős Problem #872 (weak form) [Er92c, p.47]:

In the primitive-set saturation game on {2, 3, …, n}, there exists ε > 0
such that, regardless of who moves first, the Lengthener can guarantee
at least εn moves for all sufficiently large n.
-/
theorem erdos_problem_872_weak :
    ∃ ε : ℝ, ε > 0 ∧
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ firstPlayer : Bool,
        ∃ sL : LegalStrategy872 n, ∀ sS : LegalStrategy872 n,
          (playGame872 n sL sS (n + 1) ∅ firstPlayer : ℝ) ≥ ε * (n : ℝ) :=
  sorry

/--
Erdős Problem #872 (strong form) [Er92c, p.47]:

For every ε > 0 and all sufficiently large n, regardless of who moves first,
the Lengthener can guarantee at least (1 − ε) · n / 2 moves in the
primitive-set saturation game on {2, 3, …, n}.
-/
theorem erdos_problem_872_strong :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∀ firstPlayer : Bool,
        ∃ sL : LegalStrategy872 n, ∀ sS : LegalStrategy872 n,
          (playGame872 n sL sS (n + 1) ∅ firstPlayer : ℝ) ≥ (1 - ε) * (n : ℝ) / 2 :=
  sorry

end
