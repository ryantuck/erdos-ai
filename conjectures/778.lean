import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card

/-!
# Erdős Problem #778

Alice and Bob play a game on the edges of $K_n$, alternating colouring edges
by red (Alice) and blue (Bob). Alice goes first, and wins if at the end
the largest red clique is larger than any of the blue cliques.

Does Bob have a winning strategy for $n \geq 3$? (Erdős believed the answer is yes.)

If we change the game so that Bob colours two edges after each edge that Alice
colours, but now require Bob's largest clique to be strictly larger than Alice's,
then does Bob have a winning strategy for $n > 3$?

Finally, consider the game when Alice wins if the maximum degree of the red
subgraph is larger than the maximum degree of the blue subgraph. Who wins?

Malekshahian and Spiro [MaSp24] proved that for the first game, the set of n
for which Bob wins has density at least 3/4.

References: [Gu83], [MaSp24]
-/

open SimpleGraph

noncomputable section

/-- A game state in the edge-coloring game on K_n:
    tracks which edges are colored red (Alice) and blue (Bob). -/
structure GameState778 (n : ℕ) where
  red : Finset (Sym2 (Fin n))
  blue : Finset (Sym2 (Fin n))

/-- A strategy for a player in the edge-coloring game:
    given the current game state, choose the next edge to color. -/
def Strategy778 (n : ℕ) := GameState778 n → Sym2 (Fin n)

/-- Play the standard edge-coloring game on K_n (alternating, 1 edge each, Alice first)
    to completion. Returns the final game state with all edges colored. -/
def playStandardGame778 (n : ℕ) (alice bob : Strategy778 n) : GameState778 n := sorry

/-- Play the modified (1-vs-2) game on K_n (Alice colors 1 edge, then Bob colors 2,
    repeating) to completion. Returns the final game state with all edges colored. -/
def playModifiedGame778 (n : ℕ) (alice bob : Strategy778 n) : GameState778 n := sorry

/-- The clique number of a simple graph on Fin n: the size of the largest clique. -/
def cliqueNumber778 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ¬G.CliqueFree k}

/--
Erdős Conjecture (Problem #778, Part 1) [Gu83]:

In the standard edge-coloring game on K_n (alternating, Alice first),
Bob has a winning strategy for all n ≥ 3: he can ensure his largest
blue clique is at least as large as Alice's largest red clique.
-/
theorem erdos_problem_778_part1 :
    ∀ n : ℕ, 3 ≤ n →
    ∃ bob : Strategy778 n,
      ∀ alice : Strategy778 n,
        let final := playStandardGame778 n alice bob
        cliqueNumber778 (fromEdgeSet (final.blue : Set (Sym2 (Fin n)))) ≥
        cliqueNumber778 (fromEdgeSet (final.red : Set (Sym2 (Fin n)))) :=
  sorry

/--
Erdős Conjecture (Problem #778, Part 2) [Gu83]:

In the modified game on K_n where Alice colors 1 edge (red) and Bob colors 2 edges
(blue) per round, Bob has a winning strategy for all n > 3: he can ensure his
largest blue clique is strictly larger than Alice's largest red clique.
-/
theorem erdos_problem_778_part2 :
    ∀ n : ℕ, 3 < n →
    ∃ bob : Strategy778 n,
      ∀ alice : Strategy778 n,
        let final := playModifiedGame778 n alice bob
        cliqueNumber778 (fromEdgeSet (final.blue : Set (Sym2 (Fin n)))) >
        cliqueNumber778 (fromEdgeSet (final.red : Set (Sym2 (Fin n)))) :=
  sorry

end
