-- [AI - Claude Opus 5.5]: Erdős Problem 101 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

open Filter

/-!
# Erdős Problem #101

*Source:* [erdosproblems.com/101](https://www.erdosproblems.com/101) (status **OPEN**, \$100:
"This is open, and cannot be resolved with a finite computation."; page last edited
27 December 2025, captured 2026-02-19). [Er84] [Er87b, p.170] [Er90] [Er92e] [Er95, p.181]
[Er97c, p.66]

Given $n$ points in $\mathbb{R}^2$, no five of which are on a line, the number of lines
containing four points is $o(n^2)$.

Remarks recorded on the page:
* There are sets of $n$ points with $\sim n^2/6$ collinear triples and no four points on a
  line (Burr, Grünbaum and Sloane [BGS74]; Füredi and Palásti [FuPa84]).
* Grünbaum [Gr76] constructed an example with $\gg n^{3/2}$ such lines, and Erdős speculated
  this may be the correct order of magnitude. This is false: Solymosi and Stojaković [SoSt13]
  constructed a set with no five on a line and at least $n^{2 - O(1/\sqrt{\log n})}$ lines
  containing exactly four points.
* See also Problems #102 and #669. Problem #588 asks a generalisation. This is Problem 71
  on Green's open problems list.

**Encoding.** With no five points on a line, "containing four points", "exactly four" and
"at least four" coincide. The set of such lines is finite, since each is spanned by two of
the points, so `Set.ncard` is its true size. Bounding every admissible $n$-point set by
$\varepsilon n^2$ for large $n$ says that the maximum count is $o(n^2)$.

Tags: geometry. OEIS: A006065 ("possible").

## References

* [Er84] Erdős, P., _Research problems_. Period. Math. Hungar. (1984), 101–103.
* [Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive
  geometry (Siófok, 1985) (1987), 167–177.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.
* [BGS74] Burr, S. A., Grünbaum, B. and Sloane, N. J. A., _The orchard problem_. Geometriae
  Dedicata (1974), 397–424.
* [FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of
  triangles_. Proc. Amer. Math. Soc. (1984), 561–566.
* [Gr76] Grünbaum, B., _New views on some old questions of combinatorial geometry_. Colloquio
  Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo I (1976), 451–468.
* [SoSt13] Solymosi, J. and Stojaković, M., _Many collinear k-tuples with no k+1 collinear
  points_. Discrete Comput. Geom. (2013), 811–820.

(Provenance: [BGS74], [FuPa84], [Gr76] and [SoSt13] come from the original pipeline's two
fetches of `erdosproblems.com/latex/101`, which agree. [Er84] comes from `/latex/211`. The
other Erdős keys come from sibling extractions (91, 94, 75/843).)
-/

/--
A finite point set in ℝ² has no five collinear if every five-element subset
is not collinear (i.e., no line contains five or more of the points).
-/
def NoFiveCollinear (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 5 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of 4-rich lines: the number of distinct affine lines in ℝ² that
contain at least four points from P.

An affine line is a 1-dimensional affine subspace (Module.finrank of its
direction submodule equals 1).
-/
noncomputable def fourRichLineCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) |
    Module.finrank ℝ L.direction = 1 ∧
    4 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ p ∈ L}}

/--
Erdős Problem #101 (OPEN, \$100):
Given n points in ℝ², no five of which are collinear, the number of lines
containing at least four of the points is o(n²).

Formally: for every ε > 0 there exists N such that for all n ≥ N and every
set P of n points in ℝ² with no five collinear, the count of 4-rich lines
is at most ε · n².
-/
theorem erdos_problem_101 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        NoFiveCollinear P →
        (fourRichLineCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry

/--
Grünbaum [Gr76] (PROVED): there are admissible sets with $\gg n^{3/2}$ four-point lines.
Stated for arbitrarily large `n`.
-/
theorem erdos_problem_101.variants.grunbaum :
    ∃ c : ℝ, c > 0 ∧ ∃ᶠ n : ℕ in atTop,
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n ∧ NoFiveCollinear P ∧
        c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (fourRichLineCount P : ℝ) :=
  sorry

/--
Solymosi and Stojaković [SoSt13] (PROVED): there are admissible sets with at least
$n^{2 - C/\sqrt{\log n}}$ four-point lines. Stated for arbitrarily large `n`. So `o(n²)`, if
true, cannot be improved to $O(n^{2-\delta})$.
-/
theorem erdos_problem_101.variants.solymosi_stojakovic :
    ∃ C : ℝ, C > 0 ∧ ∃ᶠ n : ℕ in atTop,
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n ∧ NoFiveCollinear P ∧
        (n : ℝ) ^ ((2 : ℝ) - C / Real.sqrt (Real.log (n : ℝ))) ≤ (fourRichLineCount P : ℝ) :=
  sorry

/--
Erdős's speculation that $n^{3/2}$ is the right order is false (PROVED, by [SoSt13]): no
bound $C n^{3/2}$ holds for all admissible sets.
-/
theorem erdos_problem_101.variants.not_three_halves :
    ¬ ∃ C : ℝ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      NoFiveCollinear P → (fourRichLineCount P : ℝ) ≤ C * (P.card : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry
