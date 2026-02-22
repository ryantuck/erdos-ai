import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Set.Card

open Complex Polynomial Set

noncomputable section

/-!
# Erdős Problem #1047

Let f ∈ ℂ[x] be a monic polynomial with m distinct roots, and let c > 0 be a
constant small enough such that { z : |f(z)| ≤ c } has m distinct connected
components. Must all these components be convex?

A question of Grunsky, reported by Erdős, Herzog, and Piranian [EHP58,p.145].

The answer is no, as shown by Pommerenke [Po61], who proved that for
f(z) = z^k(z-a) with k sufficiently large and a close to (1+1/k)k^{1/(k+1)},
the set { z : |f(z)| ≤ 1 } has two components and the one containing 0 is
not convex.

Goodman [Go66] gave further examples, including (z²+1)(z-2)² with explicit c.
-/

/--
Erdős Problem #1047 (Grunsky's question, [EHP58,p.145]):

There exists a monic polynomial f ∈ ℂ[x] and c > 0 such that the sublevel
set S = { z : ‖f(z)‖ ≤ c } has exactly as many connected components as f
has distinct roots, yet some connected component of S is not convex.

Disproved by Pommerenke [Po61].
-/
theorem erdos_problem_1047 :
    ∃ (f : Polynomial ℂ), f.Monic ∧
    ∃ (c : ℝ), c > 0 ∧
      let S := {z : ℂ | ‖Polynomial.eval z f‖ ≤ c}
      Set.ncard (connectedComponentIn S '' S) = f.roots.toFinset.card ∧
      ∃ x : ℂ, x ∈ S ∧ ¬Convex ℝ (connectedComponentIn S x) :=
  sorry

end
