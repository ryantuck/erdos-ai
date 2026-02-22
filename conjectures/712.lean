import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #712

Determine, for any k > r > 2, the value of

  ex_r(n, K_k^r) / C(n, r),

where ex_r(n, K_k^r) is the largest number of r-edges which can be placed on n
vertices so that there exists no set of k vertices which is covered by all
C(k, r) possible r-edges.

Turán proved that, when r = 2, this limit is (1/2)(1 - 1/(k-1)).

Erdős offered $500 for the determination of this value for any fixed k > r > 2,
and $1000 for 'clearing up the whole set of problems'.

See also [500] for the case r = 3 and k = 4.
-/

/-- An r-uniform hypergraph on `Fin n` is K_k^r-free if every edge has exactly r
    vertices and no k vertices span all C(k, r) possible r-element subsets. -/
def IsKkrFree {n : ℕ} (r k : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = r) ∧
  ∀ S : Finset (Fin n), S.card = k → ¬(S.powersetCard r ⊆ H)

/-- The r-uniform Turán number ex_r(n, K_k^r): the maximum number of r-element
    subsets of an n-element set such that no k vertices span all C(k, r)
    r-subsets. -/
noncomputable def exrKkr (r k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)), IsKkrFree r k H ∧ H.card = m}

/--
Erdős Conjecture (Problem #712) — Hypergraph Turán Densities:

For any k > r > 2, the Turán density

  lim_{n → ∞} ex_r(n, K_k^r) / C(n, r)

exists. Determining the value of this limit for any such k, r is the open
problem worth $500.
-/
theorem erdos_problem_712 (k r : ℕ) (hr : 2 < r) (hk : r < k) :
    ∃ L : ℝ, Tendsto
      (fun n : ℕ => (exrKkr r k n : ℝ) / (Nat.choose n r : ℝ))
      atTop (nhds L) :=
  sorry

end
