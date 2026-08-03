import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped BigOperators
open Complex Finset

noncomputable section

/--
Erdős Problem #1041 [EHP58, p.139]:

Let f(z) = ∏ᵢ (z - zᵢ) ∈ ℂ[z] with |zᵢ| < 1 for all i. Must there always
exist a path of length less than 2 in {z : |f(z)| < 1} which connects two of
the roots of f?

A problem of Erdős, Herzog, and Piranian, who proved that the sublevel set
{z : |f(z)| < 1} always has a connected component containing at least two of
the roots, counted with multiplicity (see the variant below).

This problem is OPEN — marked FALSIFIABLE ("could be disproved with a finite
counterexample") on erdosproblems.com (snapshot accessed 2026-03-06; page last
edited 06 December 2025). The statement below asserts the implicit conjecture,
i.e. the affirmative answer to the question.

Encoding notes: the monic polynomial is represented by its tuple of roots
`roots : Fin n → ℂ` (repetitions allowed), so `i ≠ j` means two roots counted
with multiplicity — for a repeated root the constant path is a legitimate
witness, exactly as in the multiset encoding of the upstream
google-deepmind/formal-conjectures formalization. The hypothesis `2 ≤ n` makes
"two of the roots" meaningful. "Length" is arc length, encoded as the total
variation `eVariationOn γ.extend (Set.Icc 0 1)` of the path.

References:
- [EHP58] Erdős, P., Herzog, F., and Piranian, G., Metric properties of
  polynomials. J. Analyse Math. (1958), 125-148.
-/
theorem erdos_problem_1041 :
    ∀ (n : ℕ) (hn : 2 ≤ n) (roots : Fin n → ℂ),
      (∀ i, ‖roots i‖ < 1) →
      ∃ (i j : Fin n), i ≠ j ∧
        ∃ (γ : Path (roots i) (roots j)),
          (∀ t, ‖∏ k : Fin n, (γ t - roots k)‖ < 1) ∧
          eVariationOn γ.extend (Set.Icc 0 1) < 2 :=
  sorry

/--
Erdős Problem #1041, component lemma [EHP58, p.139]:

Erdős, Herzog, and Piranian proved that for f(z) = ∏ᵢ (z - zᵢ) with all
|zᵢ| < 1 and n ≥ 2, the sublevel set {z : |f(z)| < 1} always has a connected
component containing at least two of the roots (with multiplicity). This is
the solved partial result stated in the remarks of the problem page.

Stated, as in the upstream formalization, via a connected subset C of the
sublevel set containing two roots — equivalent to the connected-component
form, since the connected component containing C also contains both roots.
-/
theorem erdos_problem_1041.variants.connected_component_two_roots :
    ∀ (n : ℕ) (hn : 2 ≤ n) (roots : Fin n → ℂ),
      (∀ i, ‖roots i‖ < 1) →
      ∃ C : Set ℂ, C ⊆ {z : ℂ | ‖∏ k : Fin n, (z - roots k)‖ < 1} ∧
        IsConnected C ∧
        ∃ (i j : Fin n), i ≠ j ∧ roots i ∈ C ∧ roots j ∈ C :=
  sorry

end
