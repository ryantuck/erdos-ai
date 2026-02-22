import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #565

Let R*(G) be the induced Ramsey number: the minimal m such that there is a
graph H on m vertices such that any 2-colouring of the edges of H contains
an induced monochromatic copy of G.

Is it true that R*(G) ≤ 2^{O(n)} for any graph G on n vertices?

A problem of Erdős and Rödl. Proved by Aragão, Campos, Dahia, Filipe,
and Marciano.
-/

/-- The induced Ramsey number R*(G): the minimum m such that there exists a
    graph H on m vertices where every 2-colouring of the edges of H contains
    an induced monochromatic copy of G.

    An induced monochromatic copy of G means: there is an injective
    f : V → Fin m and a colour b such that for all distinct u, v,
    G.Adj u v ↔ (H.Adj (f u) (f v) ∧ c (f u) (f v) = b). -/
noncomputable def inducedRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sInf {m : ℕ | ∃ (H : SimpleGraph (Fin m)),
    ∀ (c : Fin m → Fin m → Bool),
    (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (f : V → Fin m), Function.Injective f ∧
      ∀ u v, u ≠ v → (G.Adj u v ↔ (H.Adj (f u) (f v) ∧ c (f u) (f v) = b))}

/--
Erdős Problem #565:

There exists a constant C such that for any graph G on n vertices,
the induced Ramsey number R*(G) ≤ 2^(Cn).

A problem of Erdős and Rödl. Proved by Aragão, Campos, Dahia, Filipe,
and Marciano.
-/
theorem erdos_problem_565 :
    ∃ C : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      inducedRamseyNumber G ≤ 2 ^ (C * n) :=
  sorry

end
