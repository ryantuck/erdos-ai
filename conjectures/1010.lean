import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite

noncomputable section

open SimpleGraph

/-!
# Erdős Problem #1010

Let $t < \lfloor n/2 \rfloor$. Does every graph on $n$ vertices with
$\lfloor n^2/4 \rfloor + t$ edges contain at least $t \lfloor n/2 \rfloor$ triangles?

Rademacher proved that every graph on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$
edges contains at least $\lfloor n/2 \rfloor$ triangles. Erdős [Er62d] proved this
for $t < cn$ for some constant $c > 0$.

This was proved independently by Lovász and Simonovits [LoSi76] and Nikiforov and
Khadzhiivanov [NiKh81].
-/

/-- The number of triangles (3-cliques) in a simple graph on `Fin n`. -/
noncomputable def triangleCount {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Nat.card {s : Finset (Fin n) // G.IsNClique 3 s}

/--
Erdős Problem #1010 [Er62d]:

Let t < ⌊n/2⌋. Every graph on n vertices with ⌊n²/4⌋ + t edges contains
at least t · ⌊n/2⌋ triangles.

Proved independently by Lovász–Simonovits [LoSi76] and
Nikiforov–Khadzhiivanov [NiKh81].
-/
theorem erdos_problem_1010 (n : ℕ) (t : ℕ) (ht : t < n / 2)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ n ^ 2 / 4 + t) :
    triangleCount G ≥ t * (n / 2) :=
  sorry

end
