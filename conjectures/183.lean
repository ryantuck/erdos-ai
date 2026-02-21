import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Filter Topology

noncomputable section

/-!
# Erdős Problem #183

Let R(3;k) be the minimal n such that if the edges of K_n are coloured with
k colours then there must exist a monochromatic triangle. Determine
  lim_{k → ∞} R(3;k)^{1/k}.

Erdős offers $100 for showing that this limit is finite. The best upper bound
is R(3;k) ≤ ⌈e·k!⌉ (from a pigeonhole induction), and the best lower bound is
R(3;k) ≥ 380^{k/5} − O(1), due to Ageron et al. [ACPPRT21], giving
R(3;k)^{1/k} ≥ 380^{1/5} ≈ 3.2806.
-/

/-- The multicolor Ramsey number R(3;k): the minimum n such that every
    k-colouring of the edges of K_n contains a monochromatic triangle.
    A k-colouring is a symmetric function c : Fin n → Fin n → Fin k,
    and a monochromatic triangle is three pairwise distinct vertices
    whose three edges all receive the same colour. -/
noncomputable def multicolorRamseyTriangle (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (c : Fin n → Fin n → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a b d : Fin n), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c a b = c a d ∧ c a b = c b d}

/--
Erdős Problem #183 [Er61]:

Let R(3;k) be the minimal n such that if the edges of K_n are coloured with
k colours then there must exist a monochromatic triangle. The limit
  lim_{k → ∞} R(3;k)^{1/k}
exists.

Erdős offers $250 to determine this limit, and $100 for showing it is finite.
The best upper bound is R(3;k) ≤ ⌈e·k!⌉, and the best lower bound is
R(3;k) ≥ 380^{k/5} − O(1), giving R(3;k)^{1/k} ≥ 380^{1/5} ≈ 3.2806.
-/
theorem erdos_problem_183 :
    ∃ L : ℝ,
      Tendsto (fun k : ℕ => (multicolorRamseyTriangle k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop (nhds L) :=
  sorry

end
