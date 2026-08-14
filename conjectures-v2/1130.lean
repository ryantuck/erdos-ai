import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem #1130

For x₁, …, xₙ ∈ [-1,1] let
  l_k(x) = ∏_{i≠k}(x - xᵢ) / ∏_{i≠k}(x_k - xᵢ),
which are such that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k (the fundamental
functions of Lagrange interpolation).

Let x₀ = -1 and x_{n+1} = 1 and
  Υ(x₁,…,xₙ) = min_{0 ≤ i ≤ n} max_{x ∈ [xᵢ,x_{i+1}]} ∑_k |l_k(x)|.

The problem asks two questions:
1. Is it true that Υ(x₁,…,xₙ) ≪ log n?
2. Describe which choice of xᵢ maximise Υ(x₁,…,xₙ).

Status on erdosproblems.com/1130: PROVED ("This has been solved in the
affirmative.") — page edition 17 January 2026, accessed 2026-02-23.
Source citations on the page: [Er47, p.1172] and [Er67, p.66].
Tags: analysis | polynomials.

Remarks from the page: Erdős [Er47] could prove Υ(x₁,…,xₙ) < √n. Erdős
thought that the maximising choice is characterised by the property that the
sums λᵢ = max_{x ∈ [xᵢ,x_{i+1}]} ∑_k |l_k(x)| are all equal for 0 ≤ i ≤ n
(where x₀ = -1 and x_{n+1} = 1), which would be the same characterisation as
problem [1129]. This is true, and was proved by de Boor and Pinkus [dBPi78].
It follows by the bounds discussed in [1129] that
Υ(x₁,…,xₙ) ≤ (2/π) log n + O(1). See also [1129]
(`conjectures/1129.lean` in this repo).

References (recovered from the original pipeline's fetches of
erdosproblems.com/latex pages preserved in the session logs; volume numbers
were absent from those extractions and are deliberately not invented):
- [Er47] Erdős, P., _Some remarks on polynomials_. Bull. Amer. Math. Soc.
  (1947), 1169–1176. This problem: p. 1172.
- [Er67] Erdős, P., _Problems and results on the convergence and divergence
  properties of the Lagrange interpolation polynomials and some extremal
  problems_. Mathematica (Cluj) (1967), 65–73. This problem: p. 66.
  (Reference data from the /latex/1129 and /latex/1133 captures, which share
  this key; the /latex/1130 capture did not include an [Er67] entry.)
- [dBPi78] de Boor, C. and Pinkus, A., _Proof of the conjectures of Bernstein
  and Erdős concerning the optimal nodes for polynomial interpolation_.
  J. Approx. Theory (1978), 289–303.

NOTE: the module docstring, the docstring enrichments, and the two added
statements (`erdos_problem_1130_maximiser`, the Er47 √n-bound variant) below
are from the Fable review of 2026-08-14 and are not compile-verified (the
review container cannot run `lake build`).
-/

noncomputable section
open Finset BigOperators

namespace Erdos1130

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: Λ(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- Nodes are valid: strictly increasing and in [-1, 1]. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- The boundary sequence: -1, then the n nodes in order, then 1,
    giving n + 2 points partitioning [-1, 1] into n + 1 subintervals. -/
def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The supremum of the Lebesgue function on the i-th subinterval
    [boundary(i), boundary(i+1)] — the source's
    λ_i = max_{x ∈ [x_i, x_{i+1}]} ∑_k |l_k(x)|.

    For valid nodes each subinterval is a nonempty (possibly degenerate,
    when a node equals ±1) compact interval and Λ is continuous on it, so the
    `sSup` is a genuine attained maximum, with λ_i ≥ 1 since ∑_k l_k ≡ 1
    for n ≥ 1. -/
def localMax {n : ℕ} (nodes : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  sSup ((lebesgueFunction nodes) ''
    (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
             (boundary nodes ⟨i.val + 1, by omega⟩)))

/--
Erdős Problem #1130, question 1 (PROVED, in the affirmative):

For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k}(x-xᵢ)/(x_k-xᵢ) be the
Lagrange basis polynomials (fundamental functions of Lagrange interpolation),
satisfying l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Set x₀ = -1 and x_{n+1} = 1. Define
  Υ(x₁,...,xₙ) = min_{0 ≤ i ≤ n} max_{x ∈ [xᵢ,x_{i+1}]} ∑_k |l_k(x)|.

The problem asks: is Υ(x₁,...,xₙ) ≪ log n? (For its second question — which
choice of xᵢ maximises Υ — see `erdos_problem_1130_maximiser` below.)

This is true: by de Boor and Pinkus [dBPi78] the maximising nodes are the
equioscillating nodes of problem [1129], and it follows by the bounds
discussed in [1129] that Υ(x₁,...,xₙ) ≤ (2/π) log n + O(1). Stated as a
direct assertion of the proved (affirmative) direction, per this corpus's
raw-file convention. The `∃ i, localMax nodes i ≤ …` encodes
`min_i λ_i ≤ …` exactly, since the index set `Fin (n+1)` is finite and
nonempty. The guard n ≥ 2 is necessary: for n = 1 the Lebesgue function is
identically 1, so Υ = 1 > C·log 1 = 0 for every C.
-/
theorem erdos_problem_1130 :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∀ (nodes : Fin n → ℝ), ValidNodes nodes →
    ∃ i : Fin (n + 1), localMax nodes i ≤ C * Real.log n :=
  sorry

/--
Erdős Problem #1130, question 2 (PROVED by de Boor and Pinkus [dBPi78]):

Describe which choice of xᵢ maximise Υ(x₁,…,xₙ). Erdős thought that the
maximising choice is characterised by the property that the sums
λᵢ = max_{x ∈ [xᵢ,x_{i+1}]} ∑_k |l_k(x)| are all equal for 0 ≤ i ≤ n — the
same characterisation as problem [1129] — and de Boor and Pinkus proved
this.

Formalisation: a valid node configuration maximises Υ over all valid
configurations if and only if its local maxima λ₀, …, λₙ are all equal.
"`nodes` maximises Υ" is encoded without a separate `Υ` definition:
Υ(other) ≤ Υ(nodes) ⟺ ∃ i, ∀ j, localMax other i ≤ localMax nodes j
(both minima are attained on the finite nonempty index set `Fin (n+1)`).

NOTE: added by the Fable review from the recovered source page; not
compile-verified.
-/
theorem erdos_problem_1130_maximiser {n : ℕ} (hn : 2 ≤ n)
    (nodes : Fin n → ℝ) (hnodes : ValidNodes nodes) :
    (∀ other : Fin n → ℝ, ValidNodes other →
      ∃ i : Fin (n + 1), ∀ j : Fin (n + 1), localMax other i ≤ localMax nodes j)
    ↔ (∀ i j : Fin (n + 1), localMax nodes i = localMax nodes j) :=
  sorry

/--
Erdős Problem #1130, partial result (SOLVED, remark on the page):

Erdős [Er47] could prove Υ(x₁,…,xₙ) < √n.

Formalised in the squared form (localMax)² < n to avoid importing
`Real.sqrt`, which does not otherwise occur in this file: since every
λᵢ ≥ 0 (indeed λᵢ ≥ 1) for valid nodes, ∃ i, λᵢ² < n is equivalent to
min_i λᵢ < √n.

The page's bound is literally false at n = 1: there the Lebesgue function is
identically 1, so Υ = 1 = √1 and the strict inequality fails; hence the
guard n ≥ 2 (cf. the corrected-bound precedent of fable-review/1004). At
n = 2 the bound holds for every valid configuration: on the middle interval
[x₁,x₂] one computes Λ(x) = (|x-x₁| + |x-x₂|)/(x₂-x₁) = 1 < √2.

NOTE: added by the Fable review from the recovered source page; not
compile-verified.
-/
theorem erdos_problem_1130.variants.erdos_sqrt_bound {n : ℕ} (hn : 2 ≤ n)
    (nodes : Fin n → ℝ) (hnodes : ValidNodes nodes) :
    ∃ i : Fin (n + 1), (localMax nodes i) ^ 2 < (n : ℝ) :=
  sorry

end Erdos1130
