import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory Finset Filter BigOperators

noncomputable section

/-!
# Erdős Problem #1131

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

What is the minimal value of
  I(x₁, ..., xₙ) = ∫₋₁¹ ∑_k |l_k(x)|² dx?

In particular, is it true that min I = 2 - (1 + o(1)) / n?

Status on erdosproblems.com/1131: OPEN ("This is open, and cannot be resolved
with a finite computation.") — page edition 23 January 2026, accessed
2026-02-23. Source citations on the page: [Er61, p.67], [ESVV94], [Er95e],
[Va99, 2.45]. Tags: analysis | polynomials.

The problem has two parts: the general request "What is the minimal value of
I?" (an open-ended determine-type question, not formalizable as a precise
statement) and the specific asymptotic conjecture min I = 2 - (1+o(1))/n,
which is what `erdos_problem_1131` below formalizes, as the raw-style direct
assertion of the conjectured affirmative answer (a styled version would use
`answer(sorry) ↔`).

Remarks from the page: Erdős first conjectured this minimum was achieved by
taking the xᵢ to be the roots of the integral of the Legendre polynomial,
since Fejér [Fe32] had earlier shown these to be minimisers of
  max_{x ∈ [-1,1]} ∑_k |l_k(x)|².
This was disproved by Szabados [Sz66] for every n > 3.

Erdős, Szabados, Varma, and Vértesi [ESVV94] proved that
  2 - O((log n)² / n) ≤ min I ≤ 2 - 2/(2n-1),
where the upper bound is witnessed by the roots of the integral of the
Legendre polynomial. (NOTE: the stated upper bound fails at n = 1, where
min I = 2 but 2 - 2/(2·1-1) = 0; see `erdos_problem_1131.variants.esvv94_upper`
below, which carries the necessary guard n ≥ 2.)

References (recovered from the original pipeline's fetch of
erdosproblems.com/latex/1131 preserved in the session logs, and from sibling
files sharing the keys; volume numbers were absent from those extractions and
are deliberately not invented):
- [ESVV94] Erdős, P., Szabados, J., Varma, A. K., and Vértesi, P., _On an
  interpolation theoretical extremal problem_. Studia Sci. Math. Hungar.
  (1994), 55–60.
- [Fe32] Fejér, L., _Bestimmung derjenigen Abszissen eines Intervalles, für
  welche die Quadratsumme der Grundfunktionen der Lagrangeschen Interpolation
  im Intervalle ein möglichst kleines Maximum besitzt_. Ann. Scuola Norm.
  Sup. Pisa Cl. Sci. (2) (1932), 263–276.
- [Sz66] Szabados, J., _On a problem of P. Erdős_. Acta Math. Acad. Sci.
  Hungar. (1966), 155–157.
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221–254. (Reference data from sibling files sharing
  this key; the page's pointer "[Er61, p.67]" is recorded verbatim but could
  not be reconciled with the journal pagination from the archive.)
- [Er95e] Erdős, P. (1995). Bibliographic details not recoverable from the
  archived captures — stub.
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999). This problem: §2.45. (Reference data from sibling files sharing
  this key.)

NOTE: the module-docstring enrichment, the docstring clarifications, and the
two ESVV94-bound variants below are from the Fable review of 2026-08-14 and
are **not compile-verified** (the review container cannot run `lake build`).
The variants required one added import (`Analysis.SpecialFunctions.Log.Basic`
for `Real.log`).
-/

/-- The Lagrange basis polynomial l_k(x) for nodes `nodes : Fin n → ℝ` at index k:
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i).

    The source writes this as a single quotient of products
    (∏_{i≠k}(x - xᵢ)) / (∏_{i≠k}(x_k - xᵢ)); the factorwise form here is equal
    to it whenever the nodes are pairwise distinct (every denominator is then
    nonzero), which is the only regime in which `minLagrangeL2` uses it. -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The L² functional I(x₁,...,xₙ) = ∫₋₁¹ ∑_k l_k(x)² dx.
    (Squares of reals, so `l_k(x)^2 = |l_k(x)|²` as in the source.) -/
def lagrangeL2 {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ∑ k : Fin n, lagrangeBasis nodes k x ^ 2

/-- The minimal value of the L² functional over all choices of n distinct
    nodes in [-1, 1], encoded as `sInf`. The nodes are required to be distinct
    (`Function.Injective`) so that the Lagrange basis polynomials are
    well-defined.

    The `sInf` is a genuine infimum of a nonempty set bounded below by 0
    (the integrand is a sum of squares), for every n: at n = 0 the set is {0}
    and at n = 1 it is {2} (the single basis polynomial is the empty product 1,
    so I = ∫₋₁¹ 1 = 2). Mathematically the infimum is attained for every n
    (the functional blows up as nodes collide, so minimising sequences stay in
    a compact set of injective tuples), so `sInf` agrees with the source's
    "minimal value". -/
def minLagrangeL2 (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ,
    Function.Injective nodes ∧
    (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) ∧
    v = lagrangeL2 nodes}

/--
Erdős Problem #1131 (OPEN):
For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k} (x - xᵢ)/(x_k - xᵢ) be the
Lagrange basis polynomials. The conjecture asks whether the minimum of
I(x₁,...,xₙ) = ∫₋₁¹ ∑_k |l_k(x)|² dx satisfies min I = 2 - (1 + o(1))/n,
i.e., n · (2 - min I) → 1 as n → ∞.

Stated as the raw-style direct assertion of the conjectured affirmative
answer to the source's yes/no question ("is it true that
min I = 2 - (1+o(1))/n?"); a styled version would wrap it as
`answer(sorry) ↔ …`. The known bounds [ESVV94]
(see the variants below) give 2n/(2n-1) ≤ n·(2 - min I) ≤ O((log n)²), so
liminf ≥ 1 is known and the conjecture is that the limit exists and is
exactly 1.
-/
theorem erdos_problem_1131 :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 - minLagrangeL2 n)) atTop (nhds 1) :=
  sorry

/--
Erdős, Szabados, Varma, and Vértesi [ESVV94] (SOLVED, upper bound): for n ≥ 2,
  min I ≤ 2 - 2/(2n - 1),
witnessed by taking the nodes to be the roots of the integral of the Legendre
polynomial.

The guard n ≥ 2 is necessary: at n = 1 the functional is identically 2
(the single basis polynomial is ≡ 1), so min I = 2, while the bound would
claim min I ≤ 2 - 2/(2·1-1) = 0. At n = 2 and n = 3 the bound is attained
with equality by the witness nodes (min I = 4/3 at nodes ±1, and
I(-1,0,1) = 8/5 = 2 - 2/5), consistent with the page's statement.

NOTE: added from the recovered source page by the Fable review of 2026-08-14;
not compile-verified.
-/
theorem erdos_problem_1131.variants.esvv94_upper (n : ℕ) (hn : 2 ≤ n) :
    minLagrangeL2 n ≤ 2 - 2 / (2 * (n : ℝ) - 1) :=
  sorry

/--
Erdős, Szabados, Varma, and Vértesi [ESVV94] (SOLVED, lower bound):
  2 - O((log n)²/n) ≤ min I,
i.e. there is a constant C > 0 with 2 - C·(log n)²/n ≤ min I for all n ≥ 1.

The bound as stated holds for every n ≥ 1 (not just eventually): at n = 1 it
reads 2 - C·0 = 2 ≤ min I = 2, with equality, and any finite range of n ≥ 2
can be absorbed into C since (log n)²/n > 0 there.

NOTE: added from the recovered source page by the Fable review of 2026-08-14;
not compile-verified.
-/
theorem erdos_problem_1131.variants.esvv94_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 1 ≤ n →
      2 - C * Real.log n ^ 2 / n ≤ minLagrangeL2 n :=
  sorry

end
