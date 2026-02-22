import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph

/-- A simple graph is triangle-free (C₃-free) if no three vertices are mutually adjacent. -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v w : V, G.Adj u v → G.Adj v w → ¬G.Adj u w

/-- A simple graph is C₄-free if it contains no 4-cycle.
    The conditions `a ≠ c` and `b ≠ d` ensure the four vertices are distinct
    (the remaining distinctness conditions follow from irreflexivity of `Adj`). -/
def C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a

/-- The extremal number ex(n; {C₃, C₄}): the maximum number of edges in a
    simple graph on n vertices containing neither a triangle nor a 4-cycle. -/
noncomputable def exC3C4 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ G : SimpleGraph (Fin n),
    TriangleFree G ∧ C4Free G ∧ G.edgeSet.ncard = k}

/--
Erdős Problem #573:
Is it true that ex(n; {C₃, C₄}) ∼ (n/2)^{3/2}?

The extremal number ex(n; {C₃, C₄}) is the maximum number of edges in a graph
on n vertices that contains no triangle (C₃) and no 4-cycle (C₄).

The conjecture asserts that this quantity is asymptotically (n/2)^{3/2},
i.e. the ratio ex(n; {C₃, C₄}) / (n/2)^{3/2} tends to 1 as n → ∞.

Erdős and Simonovits proved that ex(n; {C₄, C₅}) = (n/2)^{3/2} + O(n).
Kővári, Sós, and Turán proved that the extremal number for forbidding C₄
together with any odd cycle is ∼ (n/2)^{3/2}. This problem asks whether
the same holds when only C₃ (triangles) are forbidden alongside C₄.

References: [Er71,p.103], [Er75], [ErSi82], [Er93,p.336]
-/
theorem erdos_problem_573 :
    Filter.Tendsto
      (fun n : ℕ => (exC3C4 n : ℝ) / ((n : ℝ) / 2) ^ ((3 : ℝ) / 2))
      Filter.atTop (nhds 1) :=
  sorry
