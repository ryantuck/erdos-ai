-- [AI - Claude Opus 5.5]: Erdős Problem 116 — second-pass formalization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped ENNReal
open Polynomial MeasureTheory

/-!
# Erdős Problem #116: The Area of a Lemniscate with Roots in the Unit Disc

*Source:* [erdosproblems.com/116](https://www.erdosproblems.com/116) (status **PROVED**: "This
has been solved in the affirmative."; captured 2026-02-19 as the tidied problem box).
[EHP58, p.133] [Er61, p.247] [Er82e] [Er90] [Er97c]

Let $p(z)=\prod_{i=1}^n (z-z_i)$ for $\lvert z_i\rvert \leq 1$. Is it true that
$$\lvert\{ z: \lvert p(z)\rvert <1\}\rvert>n^{-O(1)}$$
(or perhaps even $>(\log n)^{-O(1)}$)?

Remarks recorded on the page:
* Conjectured by Erdős, Herzog, and Piranian [EHP58]. The lower bound $\gg n^{-4}$ follows
  from a result of Pommerenke [Po61]. The lower bound $\gg (\log n)^{-1}$ was proved by
  Krishnapur, Lundberg, and Ramachandran [KLR25].
* Wagner [Wa88] proves, for $n\geq 3$, the existence of such polynomials with
  $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \ll_\epsilon (\log\log n)^{-1/2+\epsilon}$ for all
  $\epsilon>0$. Krishnapur, Lundberg, and Ramachandran [KLR25] improved this upper bound to
  $\ll (\log\log n)^{-1}$.
* In [EHP58] they also ask to determine the polynomials which achieve the minimum possible
  value of this measure.
* Pólya [Po28] showed the upper bound $\lvert\{ z: \lvert p(z)\rvert <1\}\rvert \leq \pi$
  always holds, and this is achieved only when the $z_i$ are identical.

**Area is Lebesgue measure.** `area` is `volume`, the Lebesgue measure on `ℂ`, so the unit disc
has area $\pi$ (`Complex.volume_ball`). The first pass used `μH[2]`. Mathlib's Hausdorff
measure is not normalised, and on the Euclidean plane `μH[2]` is $4/\pi$ times Lebesgue
measure, by the isodiametric inequality. That is harmless for `erdos_problem_116`, where
$\delta$ absorbs the constant, but Pólya's bound would read $4$ instead of $\pi$.

**Parts.** `erdos_problem_116` is the main question, `n^{-O(1)}`. The parenthetical
`(\log n)^{-O(1)}` question is `erdos_problem_116.variants.log_lower` ([KLR25]). Determining
the minimising polynomials is open-ended and has no formal target here.

Tags: polynomials, analysis.

## References

* [EHP58] Erdős, P., Herzog, F. and Piranian, G., _Metric properties of polynomials_. J.
  Analyse Math. (1958), 125–148.
* [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254.
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982),
  59–79.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul Erdős,
  I (1997), 47–67.
* [Po28] Pólya, G., _Beitrag zur Verallgemeinerung des Verzerrungssatzes auf mehrfach
  zusammenhängende Gebiete_. S.-B. Akad. Wiss. (1928), 228–232 and 280–282.
* [Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J.
  (1961), 97–115.
* [Wa88] Wagner, G., _On the area of lemniscate domains_. J. Analyse Math. (1988), 159–167.
* [KLR25] Krishnapur, M., Lundberg, E. and Ramachandran, K., _On the area of polynomial
  lemniscates_. arXiv:2503.18270 (2025).

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/116` for [EHP58],
[Po28], [Po61], [Wa88] and [KLR25]. That extraction gives [Po28]'s title as "Beitrag zue …";
"zur" is assumed to be the intended word. Sibling `/latex` extractions for [Er61], [Er82e],
[Er90] and [Er97c], which agree with upstream `116.lean`.)
-/

/-- The lemniscate interior of a complex polynomial p:
    the open sublevel set {z ∈ ℂ : |p(z)| < 1}. -/
def lemniscateInterior (p : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖p.eval z‖ < 1}

/-- The area of a subset of ℂ: its Lebesgue measure `volume`, under which the unit disc has
    area π. (The 2-dimensional Hausdorff measure `μH[2]` is 4/π times this.) -/
noncomputable def area (S : Set ℂ) : ℝ≥0∞ :=
  volume S

/--
Erdős–Herzog–Piranian Conjecture (Problem #116) [EHP58, Er61, Er82e, Er90, Er97c]:

Let p(z) = ∏ᵢ (z - zᵢ) be a polynomial of degree n ≥ 1 with all roots zᵢ
in the closed unit disk (|zᵢ| ≤ 1). Then the 2D Lebesgue measure (area) of
the lemniscate interior {z ∈ ℂ : |p(z)| < 1} satisfies

  |{z : |p(z)| < 1}| ≫ n^{-O(1)}.

That is, there exist universal constants κ > 0 and δ > 0 such that for all n ≥ 1
and all such polynomials, the area is at least δ · n^{-κ}.

The lower bound ≫ n^{-4} follows from a result of Pommerenke [Po61].
The stronger lower bound ≫ (log n)^{-1} was proved by Krishnapur, Lundberg,
and Ramachandran [KLR25], which in particular settles this conjecture.

Pólya [Po28] showed the area is always at most π, with equality only when all
roots are equal.
-/
theorem erdos_problem_116 :
    ∃ (κ δ : ℝ), 0 < δ ∧ 0 < κ ∧
    ∀ (n : ℕ), 1 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ * (n : ℝ) ^ (-κ)) ≤
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) :=
  sorry

/--
The parenthetical question, answered by Krishnapur, Lundberg and Ramachandran [KLR25] (PROVED):
the area is ≫ (log n)^{-1}, so in particular > (log n)^{-O(1)}. Here n ≥ 2, so that log n > 0.
-/
theorem erdos_problem_116.variants.log_lower :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ / Real.log n) ≤
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) :=
  sorry

/--
Pommerenke [Po61] (PROVED): the area is ≫ n^{-4}.
-/
theorem erdos_problem_116.variants.pommerenke :
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (n : ℕ), 1 ≤ n →
    ∀ (roots : Fin n → ℂ), (∀ i, ‖roots i‖ ≤ 1) →
    ENNReal.ofReal (δ * (n : ℝ) ^ (-4 : ℝ)) ≤
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) :=
  sorry

/--
Krishnapur, Lundberg and Ramachandran [KLR25] (PROVED), improving Wagner [Wa88]: for n ≥ 3 some
such polynomial has area ≪ (log log n)^{-1}. The guard n ≥ 3 makes log log n > 0.
-/
theorem erdos_problem_116.variants.klr_upper :
    ∃ K : ℝ, ∀ (n : ℕ), 3 ≤ n →
    ∃ roots : Fin n → ℂ, (∀ i, ‖roots i‖ ≤ 1) ∧
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) ≤
        ENNReal.ofReal (K / Real.log (Real.log n)) :=
  sorry

/--
Pólya [Po28] (PROVED): for every monic polynomial, the area is at most π. The roots need not
lie in the unit disc.
-/
theorem erdos_problem_116.variants.polya :
    ∀ (n : ℕ) (roots : Fin n → ℂ),
      area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) ≤ ENNReal.ofReal Real.pi :=
  sorry

/--
Pólya's equality case [Po28] (PROVED): for n ≥ 1, the area equals π only when all roots
coincide, in which case the set is a unit disc.
-/
theorem erdos_problem_116.variants.polya_equality :
    ∀ (n : ℕ), 1 ≤ n → ∀ roots : Fin n → ℂ,
      (area (lemniscateInterior (∏ i : Fin n, (X - C (roots i)))) = ENNReal.ofReal Real.pi ↔
        ∀ i j, roots i = roots j) :=
  sorry
