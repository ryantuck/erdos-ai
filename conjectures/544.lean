import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open SimpleGraph Filter

noncomputable section

/-!
# Erdős Problem #544

Show that R(3,k+1) - R(3,k) → ∞ as k → ∞.
Similarly, prove or disprove that R(3,k+1) - R(3,k) = o(k).

A problem of Erdős and Sós. See also [165] and [1014].
-/

/-- The Ramsey number R(3,k): the minimum N such that every simple graph
    on N vertices contains either a triangle (3-clique) or an independent
    set of size k (a k-clique in the complement). -/
noncomputable def ramseyR3_544 (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)), ¬G.CliqueFree 3 ∨ ¬Gᶜ.CliqueFree k}

/--
Erdős Problem #544 (Part 1) [Er81c][Er93,p.339]:

Show that R(3,k+1) - R(3,k) → ∞ as k → ∞.

That is, the consecutive differences of the Ramsey numbers R(3,k)
tend to infinity.
-/
theorem erdos_problem_544a :
    Tendsto (fun k : ℕ => (ramseyR3_544 (k + 1) : ℤ) - (ramseyR3_544 k : ℤ))
      atTop atTop :=
  sorry

/--
Erdős Problem #544 (Part 2) [Er81c][Er93,p.339]:

Prove or disprove that R(3,k+1) - R(3,k) = o(k), i.e.,
  (R(3,k+1) - R(3,k)) / k → 0 as k → ∞.
-/
theorem erdos_problem_544b :
    Tendsto (fun k : ℕ => ((ramseyR3_544 (k + 1) : ℝ) - (ramseyR3_544 k : ℝ)) / (k : ℝ))
      atTop (nhds 0) :=
  sorry

end
