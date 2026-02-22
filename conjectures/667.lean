import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Choose.Basic

noncomputable section

open SimpleGraph Finset Filter Classical

/-!
# Erdős Problem #667

Let p, q ≥ 1 be fixed integers. Define H(n) = H(n; p, q) to be the largest m
such that any graph on n vertices where every set of p vertices spans at least
q edges must contain a complete graph on m vertices.

Is c(p, q) = liminf_{n → ∞} log(H(n; p, q)) / log(n) a strictly increasing
function of q for 1 ≤ q ≤ C(p-1, 2) + 1?

A problem of Erdős, Faudree, Rousseau, and Schelp [Er97f].
-/

/-- The number of edges of G within a subset S of vertices:
    the count of pairs (u, v) with u < v, both in S, and G.Adj u v. -/
noncomputable def edgesInSubset667 {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter fun e => e.1 < e.2 ∧ G.Adj e.1 e.2).card

/-- A graph on n vertices has the (p, q)-density property if every p-element
    subset spans at least q edges. -/
def hasDensityProperty667 {n : ℕ} (G : SimpleGraph (Fin n)) (p q : ℕ) : Prop :=
  ∀ S : Finset (Fin n), S.card = p → edgesInSubset667 G S ≥ q

/-- H(n; p, q): the largest m such that every graph on n vertices with the
    (p, q)-density property must contain a clique of size m. -/
noncomputable def erdosH (n p q : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ G : SimpleGraph (Fin n),
    hasDensityProperty667 G p q → ∃ S : Finset (Fin n), G.IsNClique m S}

/-- c(p, q) = liminf_{n → ∞} log(H(n; p, q)) / log(n). -/
noncomputable def erdosC667 (p q : ℕ) : ℝ :=
  Filter.liminf (fun n : ℕ => Real.log (erdosH n p q : ℝ) / Real.log (n : ℝ))
    Filter.atTop

/--
Erdős Problem #667 [Er97f]:

Is c(p, q) strictly increasing in q for 1 ≤ q ≤ C(p-1, 2) + 1?

That is, for all q with 1 ≤ q < C(p-1, 2) + 1, we have c(p, q) < c(p, q+1).
-/
theorem erdos_problem_667 (p : ℕ) (hp : p ≥ 1) (q : ℕ)
    (hq1 : 1 ≤ q) (hq2 : q < (p - 1).choose 2 + 1) :
    erdosC667 p q < erdosC667 p (q + 1) :=
  sorry

end
