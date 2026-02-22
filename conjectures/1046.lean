import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Topology.Connected.Basic

open Complex Polynomial Metric Set

noncomputable section

/-!
# Erdős Problem #1046

Let f ∈ ℂ[x] be a monic polynomial and E = { z : |f(z)| < 1 }.
If E is connected then is E contained in a disc of radius 2?

A problem of Erdős, Herzog, and Piranian [EHP58]. The answer is yes,
and in fact the centre of this disc can be taken to be (z₁+⋯+zₙ)/n,
where the zᵢ are the roots of f, as shown by Pommerenke [Po59].

Their additional conjecture that the width of {z : |f(z)| ≤ 1} is
always at most 2 was disproved by Pommerenke.
-/

/--
Erdős Problem #1046 [EHP58,p.143]:

For any monic polynomial f ∈ ℂ[x], if the set E = { z ∈ ℂ : ‖f(z)‖ < 1 }
is connected, then E is contained in a closed disc of radius 2.

Proved by Pommerenke [Po59].
-/
theorem erdos_problem_1046 (f : Polynomial ℂ) (hf : f.Monic)
    (hconn : IsConnected {z : ℂ | ‖Polynomial.eval z f‖ < 1}) :
    ∃ c : ℂ, {z : ℂ | ‖Polynomial.eval z f‖ < 1} ⊆ closedBall c 2 :=
  sorry

end
