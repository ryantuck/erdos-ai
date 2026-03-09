import Mathlib.Data.Nat.Totient
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

noncomputable section

/--
V(x) counts the number of n ≤ x such that φ(m) = n is solvable for some m,
i.e., the number of totient values up to x.

We bound the search for m by (x * x + 1) since for any n ≤ x in the range
of Euler's totient, there exists some m with φ(m) = n; the bound makes
the definition computable.
-/
def totientValues (x : ℕ) : ℕ :=
  {n ∈ Finset.range (x + 1) | ∃ m ∈ Finset.range (x * x + 1), Nat.totient m = n}.card

/--
Erdős Problem #416 [Er74b, Er79e, ErGr80, Er98]:

Let V(x) count the number of n ≤ x such that φ(m) = n is solvable.
Does V(2x) / V(x) → 2?

Pillai proved V(x) = o(x). Erdős proved V(x) = x(log x)^{-1+o(1)}.
Maier and Pomerance (1988) and Ford (1998) gave sharper estimates,
but an asymptotic formula and the ratio limit remain open.
-/
theorem erdos_problem_416 :
    Tendsto (fun x : ℕ => (totientValues (2 * x) : ℝ) / (totientValues x : ℝ))
      atTop (nhds 2) :=
  sorry
