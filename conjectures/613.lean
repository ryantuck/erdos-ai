import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph Classical

noncomputable section

/-!
# Erdős Problem #613

Let n ≥ 3 and G be a graph with C(2n+1,2) - C(n,2) - 1 edges.
Must G be the union of a bipartite graph and a graph with maximum degree
less than n?

Equivalently, if F is the family of all odd cycles and K_{1,n} is the star
with n+1 vertices, this asks whether
  r̂(K_{1,n}, F) = C(2n+1,2) - C(n,2)
where r̂ is the size Ramsey number.

This is false, as disproved by Pikhurko [Pi01], who proved
  n² + 0.577·n^{3/2} < r̂(K_{1,n}, F) < n² + √2·n^{3/2} + n
for all large n. The conjectured bound already fails for n = 5.

Tags: graph theory, ramsey
-/

/--
**Erdős Problem #613** (Original conjecture, DISPROVED):

For n ≥ 3, every graph G with C(2n+1,2) - C(n,2) - 1 edges can be written as
the union of a bipartite graph and a graph with maximum degree less than n.
-/
theorem erdos_problem_613 (n : ℕ) (hn : n ≥ 3)
    (m : ℕ) (G : SimpleGraph (Fin m)) :
    G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 →
    ∃ (G₁ G₂ : SimpleGraph (Fin m)),
      G₁ ⊔ G₂ = G ∧ G₁.Colorable 2 ∧ G₂.maxDegree < n :=
  sorry

/--
**Erdős Problem #613** (Disproof, Pikhurko [Pi01]):

There exists n ≥ 3 and a graph G with C(2n+1,2) - C(n,2) - 1 edges that
cannot be written as the union of a bipartite graph and a graph with maximum
degree less than n.
-/
theorem erdos_problem_613_disproof :
    ∃ (n : ℕ), n ≥ 3 ∧
    ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
      G.edgeFinset.card = Nat.choose (2 * n + 1) 2 - Nat.choose n 2 - 1 ∧
      ¬∃ (G₁ G₂ : SimpleGraph (Fin m)),
        G₁ ⊔ G₂ = G ∧ G₁.Colorable 2 ∧ G₂.maxDegree < n :=
  sorry

end
