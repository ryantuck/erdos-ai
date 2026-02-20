import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical

/--
The set A of non-negative integers whose base-3 representation uses only digits 0 and 1.
Equivalently, A = {∑ εₖ · 3^k : εₖ ∈ {0,1}}.
-/
def baseThreeZeroOne : Set ℕ :=
  { n : ℕ | ∀ d ∈ Nat.digits 3 n, d ≤ 1 }

/--
The set B of non-negative integers whose base-4 representation uses only digits 0 and 1.
Equivalently, B = {∑ εₖ · 4^k : εₖ ∈ {0,1}}.
-/
def baseFourZeroOne : Set ℕ :=
  { n : ℕ | ∀ d ∈ Nat.digits 4 n, d ≤ 1 }

/--
The lower asymptotic density of A ⊆ ℕ:
  d(A) = liminf_{N→∞} |A ∩ {0, 1, ..., N-1}| / N
-/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/--
Erdős Problem #125 (Burr, Erdős, Graham, Li [BEGL96]):

Let A = {∑ εₖ 3^k : εₖ ∈ {0,1}} be the set of non-negative integers with only
digits 0 and 1 in base 3, and B = {∑ εₖ 4^k : εₖ ∈ {0,1}} be the set with only
digits 0 and 1 in base 4. The conjecture is that the sumset A + B has positive
lower density.

Melfi [Me01] showed |C ∩ [1,x]| ≫ x^0.965, improved by Hasler–Melfi [HaMe24]
to |C ∩ [1,x]| ≫ x^0.9777, where C = A + B. Hasler–Melfi also showed the
lower density of C is at most 1015/1458 ≈ 0.696.
-/
theorem erdos_problem_125 :
    0 < lowerDensity (Set.image2 (· + ·) baseThreeZeroOne baseFourZeroOne) :=
  sorry
