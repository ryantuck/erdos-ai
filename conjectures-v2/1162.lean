import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic

open Filter Real

noncomputable section

/-!
# Erdős Problem #1162

Give an asymptotic formula for the number of subgroups of Sₙ.
Is there a statistical theorem on their order?

A problem of Erdős and Turán [Va99, 5.73]. Status on erdosproblems.com: OPEN
(page edition 23 January 2026; the teorth/erdosproblems metadata mirror confirms
`open`, last update 2026-01-23).

Let f(n) count the number of subgroups of Sₙ.
Pyber [Py93] proved that log f(n) ≍ n².
Roney-Dougal and Tracey [RoTr25] proved that f(n) = 2^{(1/16 + o(1))n²}, i.e.
log₂ f(n) = (1/16 + o(1))n². (The source page writes "log f(n) = (1/16+o(1))n²";
the constant 1/16 belongs to the base-2 logarithm — in natural log the statement
reads ln f(n) = ((ln 2)/16 + o(1))n².)

The second part of the problem ("a statistical theorem on their order") is vague
as stated; see Erdős Problem #1163 for one formalization of that aspect
(the arithmetic structure of subgroup orders of Sₙ).

References (stubs recovered from archived pipeline logs; not independently
verified against the live bibliography):

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999.

[Py93] Pyber, L., _Asymptotic results for permutation groups_ (1993), 197–219.
(Publication venue/volume absent from the recovered data.)

[RoTr25] Roney-Dougal, C. and Tracey, G., _Subgroups of symmetric groups:
enumeration and asymptotic properties_. arXiv:2503.05416 (2025).

Tags: group theory
-/

/-- The number of subgroups of the symmetric group Sₙ. -/
noncomputable def numSubgroups (n : ℕ) : ℕ :=
  Nat.card (Subgroup (Equiv.Perm (Fin n)))

/--
Erdős Problem #1162 (partially resolved by Roney-Dougal and Tracey [RoTr25]):

log₂ f(n) / n² → 1/16 as n → ∞, where f(n) is the number of subgroups of Sₙ;
equivalently, since `Real.log` is the natural logarithm,
ln f(n) / n² → (ln 2)/16.

The full problem, asking for an asymptotic formula for f(n) and a statistical
theorem on the orders of subgroups, remains open.
-/
theorem erdos_problem_1162 :
    Tendsto (fun n : ℕ => Real.log (numSubgroups n : ℝ) / ((n : ℝ) ^ 2))
      atTop (nhds (Real.log 2 / 16)) :=
  sorry

/--
Pyber's earlier result [Py93]: log f(n) ≍ n², where f(n) is the number of
subgroups of Sₙ — there are positive constants c₁, c₂ with
c₁ n² ≤ log f(n) ≤ c₂ n² for all sufficiently large n. (The ≍ relation is
independent of the logarithm base.) Solved; superseded by [RoTr25].
-/
theorem erdos_problem_1162.variants.pyber :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * (n : ℝ) ^ 2 ≤ Real.log (numSubgroups n : ℝ) ∧
      Real.log (numSubgroups n : ℝ) ≤ c₂ * (n : ℝ) ^ 2 :=
  sorry

end
