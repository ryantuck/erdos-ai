import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

open Finset

/--
An edge colouring of the complete graph on `Fin n` with `r` colours,
represented as a symmetric function on distinct vertices.
-/
structure EdgeColoring (n r : ℕ) where
  color : Fin n → Fin n → Fin r
  symm : ∀ i j, color i j = color j i

/--
The set of colours appearing on the edges of the induced complete subgraph
on a vertex subset S.
-/
def colorsUsed {n r : ℕ} (c : EdgeColoring n r) (S : Finset (Fin n)) : Finset (Fin r) :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)).image (fun p => c.color p.1 p.2)

/--
Erdős Problem #617 [ErGy99, Er99]:

Let r ≥ 3. If the edges of K_{r²+1} are r-coloured then there exist r+1
vertices with at least one colour missing on the edges of the induced K_{r+1}.

In other words, there is no balanced colouring. Erdős and Gyárfás proved it
for r = 3 and r = 4 (and observed it is false for r = 2), and showed this
property fails for infinitely many r if r² + 1 is replaced by r².
-/
theorem erdos_problem_617
    (r : ℕ) (hr : r ≥ 3)
    (c : EdgeColoring (r ^ 2 + 1) r) :
    ∃ S : Finset (Fin (r ^ 2 + 1)),
      S.card = r + 1 ∧
      colorsUsed c S ≠ Finset.univ :=
  sorry
