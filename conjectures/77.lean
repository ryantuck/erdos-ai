import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Topology

noncomputable section

/-!
# Erdős Problem #77

If R(k) is the Ramsey number for K_k, the minimal n such that every 2-colouring
of the edges of K_n contains a monochromatic copy of K_k, then find the value of
  lim_{k → ∞} R(k)^{1/k}.

Erdős proved √2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 4.
The upper bound has been improved to 3.7992... by Gupta, Ndiaye, Norin, and
Wei [GNNW24], building on the breakthrough of Campos, Griffiths, Morris,
and Sahasrabudhe [CGMS23] who first improved the upper bound below 4.

Erdős offered $100 for a proof that this limit exists, and $250 for finding
its value.

Tags: graph theory, ramsey theory
-/

/-- The diagonal Ramsey number R(k): the minimum N such that for every
    symmetric 2-colouring of the edges of K_N, there is a monochromatic
    clique of size k in some colour. -/
noncomputable def diagonalRamseyNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Bool), (∀ i j, c i j = c j i) →
    ∃ (b : Bool) (S : Finset (Fin N)), S.card = k ∧
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → c i j = b}

/--
Erdős Problem #77 [Er61]:

The limit lim_{k → ∞} R(k)^{1/k} exists, where R(k) is the diagonal
Ramsey number.

Formulated as: there exists a real number L such that R(k)^{1/k} → L
as k → ∞.
-/
theorem erdos_problem_77 :
    ∃ L : ℝ, Tendsto (fun k : ℕ =>
      (diagonalRamseyNumber k : ℝ) ^ ((1 : ℝ) / (k : ℝ))) atTop (nhds L) :=
  sorry

end
