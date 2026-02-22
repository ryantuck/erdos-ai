import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph

noncomputable section

/-- A simple graph G contains a cycle of length m (m ≥ 3) if there exist m
    distinct vertices v₀, …, v_{m-1} such that v_i is adjacent to v_{(i+1) mod m}
    for all i. -/
def ContainsCycleOfLength {V : Type*} (G : SimpleGraph V) (m : ℕ) (_ : m ≥ 3) : Prop :=
  ∃ (f : Fin m → V), Function.Injective f ∧
    ∀ i j : Fin m, j.val = (i.val + 1) % m → G.Adj (f i) (f j)

/-- The extremal number ex(n; {C_{2k-1}, C_{2k}}): the maximum number of edges in a
    simple graph on n vertices containing no cycle of length 2k-1 or 2k. -/
noncomputable def exConsecutiveCycles (k : ℕ) (hk : k ≥ 2) (n : ℕ) : ℕ :=
  sSup {e : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsCycleOfLength G (2 * k - 1) (by omega) ∧
    ¬ContainsCycleOfLength G (2 * k) (by omega) ∧
    G.edgeSet.ncard = e}

/--
Erdős Problem #574:
Is it true that, for k ≥ 2,
  ex(n; {C_{2k-1}, C_{2k}}) = (1 + o(1)) · (n/2)^{1 + 1/k}?

The extremal number ex(n; {C_{2k-1}, C_{2k}}) is the maximum number of edges in a graph
on n vertices that contains no cycle of length 2k-1 and no cycle of length 2k.

The conjecture asserts that for each fixed k ≥ 2, this extremal number is
asymptotically (n/2)^{1+1/k}, i.e. the ratio tends to 1 as n → ∞.

The case k = 2 (forbidding C₃ and C₄) is Erdős Problem #573.

A problem of Erdős and Simonovits.

References: [ErSi82]
-/
theorem erdos_problem_574 (k : ℕ) (hk : k ≥ 2) :
    Filter.Tendsto
      (fun n : ℕ => (exConsecutiveCycles k hk n : ℝ) / ((n : ℝ) / 2) ^ (1 + 1 / (k : ℝ)))
      Filter.atTop (nhds 1) :=
  sorry

end
