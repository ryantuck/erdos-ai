import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section
open SimpleGraph Classical Filter

namespace Erdos1091

/-- A graph G contains an odd cycle with at least `d` diagonals.

An odd cycle of length 2m+3 (≥ 3) is given by an injective map f : Fin (2m+3) → V
where consecutive vertices (cyclically) are adjacent in G. A diagonal is an edge
of G between two cycle vertices that are not consecutive in the cycle. -/
def HasOddCycleWithDiagonals {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (f : Fin (2 * m + 3) → V),
    Function.Injective f ∧
    (∀ i : Fin (2 * m + 3),
      G.Adj (f i) (f ⟨(i.val + 1) % (2 * m + 3), Nat.mod_lt _ (by omega)⟩)) ∧
    d ≤ (Finset.univ.filter (fun p : Fin (2 * m + 3) × Fin (2 * m + 3) =>
      p.1.val < p.2.val ∧
      G.Adj (f p.1) (f p.2) ∧
      p.2.val ≠ (p.1.val + 1) % (2 * m + 3) ∧
      p.1.val ≠ (p.2.val + 1) % (2 * m + 3))).card

/--
Erdős Problem #1091, Part 1 (proved by Voss [Vo82]):

Let G be a K₄-free graph with chromatic number 4. Then G contains an odd cycle
with at least two diagonals.

Erdős originally asked about one diagonal, proved by Larson [La79]. The
pentagonal wheel shows that three diagonals cannot be guaranteed.
-/
theorem erdos_problem_1091a (n : ℕ) (G : SimpleGraph (Fin n))
    (hK4 : G.CliqueFree 4) (hχ : G.chromaticNumber = (4 : ℕ∞)) :
    HasOddCycleWithDiagonals G 2 :=
  sorry

/--
Erdős Problem #1091, Part 2 (Open) [Er76c,p.4]:

Is there a function f : ℕ → ℕ with f(r) → ∞ such that every graph G with
chromatic number 4, in which every induced subgraph on ≤ r vertices has
chromatic number ≤ 3, contains an odd cycle with at least f(r) diagonals?
-/
theorem erdos_problem_1091b :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (4 : ℕ∞) →
        (∀ S : Finset (Fin n), S.card ≤ r →
          (G.induce (↑S : Set (Fin n))).chromaticNumber ≤ (3 : ℕ∞)) →
        HasOddCycleWithDiagonals G (f r) :=
  sorry

end Erdos1091
