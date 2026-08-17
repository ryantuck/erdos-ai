import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

open Filter Asymptotics

noncomputable section

namespace Erdos1178

/-!
# Erdős Problem #1178

For r ≥ 3, let d_r(e) be the minimal d such that ex_r(n, F) = o(n²),
where F is the family of r-uniform hypergraphs on d vertices with e edges.

Prove that d_r(e) = (r-2)e + 3 for all r, e ≥ 3.

A conjecture of Brown, Erdős, and Sós [BES73], who proved d_r(e) ≥ (r-2)e + 3.
Erdős, Frankl, and Rödl [EFR86] proved d_r(3) = 3(r-2)+3 for all r ≥ 3.
(For the special case e = 3, a related result was also proved by Ruzsa and Szemerédi [RuSz78].)

## References

[BES73] Brown, W. G., Erdős, P., and Sós, V. T.,
        "Some extremal problems on r-graphs,"
        *New Directions in the Theory of Graphs* (1973).

[RuSz78] Ruzsa, I. Z., and Szemerédi, E.,
         "The number of small gaps between primes,"
         *Combinatorica* (1978).

[EFR86] Erdős, P., Frankl, P., and Rödl, V.,
        "The asymptotic number of graphs not containing a fixed subgraph and a problem for hypergraphs,"
        *Graphs and Combinatorics* (1986).

Tags: graph theory, hypergraphs
-/

/-- An r-uniform hypergraph on vertex type V is a set of r-element subsets of V. -/
def IsRUniform (r : ℕ) {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = r

/-- An r-uniform hypergraph on n vertices contains a sub-hypergraph on d vertices
    with e edges: there exist d vertices in Fin n such that the hypergraph has
    at least e r-uniform edges entirely within those d vertices. Since F_r(d,e)
    contains all r-uniform hypergraphs on d vertices with e edges, avoiding F means
    no d vertices span e or more r-uniform edges. -/
def ContainsConfig (d e n : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = d ∧ e ≤ (E.filter (fun edge => edge ⊆ S)).card

/-- The r-uniform Turán number ex_r(n; d, e): the maximum number of edges in an
    r-uniform hypergraph on n vertices that contains no r-uniform sub-hypergraph
    on d vertices with e edges (i.e., avoids the Brown-Erdős-Sós family F_r(d,e)). -/
noncomputable def turanNumber (r n d e : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
    IsRUniform r E ∧ ¬ ContainsConfig d e n E ∧ E.card = m}

/-- The minimal d such that the r-uniform Turán number ex_r(n; d, e) = o(n²)
    as n → ∞. -/
noncomputable def minD (r e : ℕ) : ℕ :=
  sInf {d : ℕ | (fun n : ℕ => (turanNumber r n d e : ℝ)) =o[atTop]
                (fun n : ℕ => (n : ℝ) ^ 2)}

/--
Erdős Problem #1178 [BES73] [EFR86]:

For r, e ≥ 3, the minimal d such that the r-uniform Turán number
ex_r(n, F) = o(n²) (where F is the family of all r-uniform hypergraphs on d vertices
with e edges) equals (r-2)·e + 3.

Here turanNumber r n d e is the maximum number of edges in an r-uniform hypergraph
on n vertices avoiding all configurations on d vertices with e edges: formally, there
is no d-element set S ⊆ Fin n with e or more r-uniform edges in S. minD r e is the
least such d.

Brown, Erdős, and Sós proved the lower bound d_r(e) ≥ (r-2)·e + 3.
Erdős, Frankl, and Rödl proved the case e = 3: d_r(3) = 3(r-2)+3 for all r ≥ 3.
-/
theorem erdos_problem_1178 (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    minD r e = (r - 2) * e + 3 :=
  sorry

end Erdos1178

end
