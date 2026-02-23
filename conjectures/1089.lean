import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

noncomputable section
open Classical Finset Filter

namespace Erdos1089

/-- The set of distinct distances determined by a finite set of points
    in d-dimensional Euclidean space. -/
noncomputable def distinctDistances {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Finset ℝ :=
  S.biUnion (fun a => (S.erase a).image (fun b => dist a b))

/-- The number of distinct distances determined by a finite set of points. -/
noncomputable def distinctDistanceCount {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (distinctDistances S).card

/-- g_d(n) is the minimal number of points in ℝ^d such that any collection of
    that many points determines at least n distinct distances. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (S : Finset (EuclideanSpace ℝ (Fin d))), S.card ≥ m →
    distinctDistanceCount S ≥ n}

/--
Erdős Problem #1089 (Kelly's question, resolved):
Let g_d(n) be minimal such that every collection of g_d(n) points in ℝ^d determines
at least n distinct distances. The limit lim_{d→∞} g_d(n) / d^{n-1} exists and
equals 1/(n-1)! for all n ≥ 2.

The lower bound C(d+1, n-1) + 1 ≤ g_d(n) is due to Aletheia-Zomlefer [Fe26]
and the upper bound g_d(n) ≤ C(d+n-1, n-1) + 1 is due to Bannai, Bannai,
and Stanton [BBS83].
-/
theorem erdos_problem_1089 (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
      atTop (nhds (1 / (Nat.factorial (n - 1) : ℝ))) :=
  sorry

end Erdos1089

end
