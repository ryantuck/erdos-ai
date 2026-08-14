import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #1129

For $x_1, \ldots, x_n \in [-1,1]$ let
$$l_k(x) = \frac{\prod_{i \neq k}(x - x_i)}{\prod_{i \neq k}(x_k - x_i)},$$
which are such that $l_k(x_k) = 1$ and $l_k(x_i) = 0$ for $i \neq k$.
Describe which choice of $x_i$ minimise
$$\Lambda(x_1, \ldots, x_n) = \max_{x \in [-1,1]} \sum_k |l_k(x)|.$$

Status on erdosproblems.com/1129: PROVED ("This has been solved in the
affirmative."; page edition 23 January 2026, accessed 2026-02-23). Source
citations on the page: [Er47, p.1171] and [Er67, p.66]. Tags: analysis,
polynomials. See also erdosproblems.com problems [671], [1130], and [1132].

The $l_k$ are the fundamental functions of Lagrange interpolation and
$\Lambda$ is the Lebesgue constant. Page remarks: Faber [Fa14] proved
$\Lambda \gg \log n$ for all choices of $x_i$; Bernstein [Be31] proved
$\Lambda > (\frac{2}{\pi} - o(1)) \log n$; Erdős [Er61c] improved this to
$\Lambda > \frac{2}{\pi} \log n - O(1)$, best possible since the roots of the
$n$th Chebyshev polynomial give $\Lambda < \frac{2}{\pi} \log n + O(1)$.
Erdős thought the minimising choice is characterised by the property that the
sums $\lambda_i = \max_{x \in [x_i, x_{i+1}]} \sum_k |l_k(x)|$ are all equal
for $0 \le i \le n$ (where $x_0 = -1$ and $x_{n+1} = 1$); this conjecture was
also made by Bernstein [Be31]. Kilgore and Cheney [KiCh76] proved that there
exist $x_i$ for which all $\lambda_i$ are equal; Kilgore [Ki77] proved that
$\Lambda$ is minimised only when all $\lambda_i$ are equal; de Boor and
Pinkus [dBPi78] proved that there exists a unique minimising choice of $x_i$.
If $x_1 = -1$ and $x_n = 1$ (a *canonical* choice) then there is a unique
minimising set of $x_i$, symmetric around $0$; the exact minimising canonical
choice is known only for $n \le 4$: for $n = 2$ it is $-1, 1$ (with
$\Lambda = 1$); for $n = 3$ it is $-1, 0, 1$ (with $\Lambda = 5/4$, Bernstein
[Be31]); for $n = 4$ it is $-1, -t, t, 1$ with $t \approx 0.4177$ an explicit
algebraic constant (Rack–Vajda [RaVa15], $\Lambda \approx 1.4229$). In [Er67]
Erdős also posed the complex variant on the unit circle, solved by Brutman
[Br80] (odd $n$) and Brutman–Pinkus [BrPi80] (even $n$): the $n$th roots of
unity are optimal.

## Correction applied by the fable review (2026-08-14)

The first-pass theorem asserted, for nodes ranging over *all* strictly
increasing configurations in $[-1,1]$, that the minimiser of $\Lambda$ is
unique and satisfies the $(n+1)$-interval equioscillation property. That
statement is **false for every $n \ge 3$**: $\Lambda$'s local maxima between
nodes are invariant under affine maps of the node set (each $l_k$ depends
only on ratios of differences), so shrinking an optimal canonical
configuration slightly keeps every inter-node local maximum equal to the
optimal value $\Lambda^*$ while the two outer maxima rise continuously from
$1 < \Lambda^*$, producing a *continuum* of minimisers. Concretely for
$n = 3$: every configuration $(-s, 0, s)$ with $2\sqrt{2}/3 \le s \le 1$ has
$\Lambda = 5/4$ (on $[-s,s]$ the Lebesgue function is $1 + x(s-x)/s^2$ up to
symmetry, with maximum $5/4$ independent of $s$; the value at $\pm 1$ is
$(2 - s^2)/s^2$, which is $\le 5/4$ iff $s \ge 2\sqrt{2}/3$), so the
minimiser is not unique. Moreover the minimiser $(-1, 0, 1)$ has degenerate
outer subinterval $[x_0, x_1] = \{-1\}$ with $\lambda_0 = L(-1) = 1 \ne 5/4$,
so the $(n+1)$-interval equioscillation property also fails at a minimiser
(both facts verified numerically in fable-review/1129.md). The theorems of
[KiCh76], [Ki77], [dBPi78] live in the canonical normalisation $x_1 = -1$,
$x_n = 1$, with equioscillation over the $n - 1$ intervals between
consecutive nodes; the corrected statement below is in that setting. The
minimum *value* over all configurations is unchanged by the normalisation
(affine invariance again), so the corrected `opt` still minimises over all
valid configurations.

References (bibliographic data recovered from the original pipeline's fetch
of erdosproblems.com/latex/1129, preserved in the session logs; [Er47]/[Er67]
data carried over from sibling files `deepmind/deepmind/1130.lean` and
`deepmind/deepmind/1133.lean`, which cite the same keys; volume numbers were
absent from the recovered extraction and are not invented here):

- [Er47] Erdős, P., _Some remarks on polynomials_. Bull. Amer. Math. Soc.
  (1947), 1169–1176. This problem: p. 1171.
- [Er67] Erdős, P., _Problems and results on the convergence and divergence
  properties of the Lagrange interpolation polynomials and some extremal
  problems_. Mathematica (Cluj) (1967), 65–73. This problem: p. 66.
- [Fa14] Faber, G., _Über die interpolatorische Darstellung stetiger
  Funktionen_. Jahresb. der Deutschen Math. Ver. (1914), 190–210.
- [Be31] Bernstein, S., _Sur la limitation des valeurs d'un polynome
  $P_n(x)$ de degré $n$ sur tout un segment par ses valeurs en $(n+1)$
  points du segment_. Izv. Akad. Nauk. SSSR (1931), 1025–1050.
- [Er61c] Erdős, P., _Problems and results on the theory of
  interpolation. II_. Acta Math. Acad. Sci. Hungar. (1961), 235–244.
- [KiCh76] Kilgore, T. A. and Cheney, E. W., _A theorem on interpolation in
  Haar subspaces_. Aequationes Math. (1976), 391–400.
- [Ki77] Kilgore, T. A., _Optimization of the norm of the Lagrange
  interpolation operator_. Bull. Amer. Math. Soc. (1977), 1069–1071.
- [dBPi78] de Boor, C. and Pinkus, A., _Proof of the conjectures of Bernstein
  and Erdős concerning the optimal nodes for polynomial interpolation_.
  J. Approx. Theory (1978), 289–303.
- [Br80] Brutman, L., _On the polynomial and rational projections in the
  complex plane_. SIAM J. Numer. Anal. (1980), 366–372.
- [BrPi80] Brutman, L. and Pinkus, A., _On the Erdős conjecture concerning
  minimal norm interpolation on the unit circle_. SIAM J. Numer. Anal.
  (1980), 373–375.

NOTE: the corrected statement, the two new definitions, and the four variants
below are from the fable review of 2026-08-14 and are **not compile-verified**
(the review container cannot run `lake build`).
-/

noncomputable section
open Finset BigOperators

namespace Erdos1129

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i)

    (For non-injective `nodes` a zero denominator makes the corresponding
    factor 0 by Lean's division convention; all uses below are guarded by
    `StrictMono`.) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: L(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The Lebesgue constant: Λ(nodes) = sup_{x ∈ [-1,1]} ∑_k |l_k(x)|
    (well-defined: the image of the compact nonempty interval under the
    continuous Lebesgue function is nonempty and bounded above). -/
def lebesgueConstant {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  sSup ((lebesgueFunction nodes) '' (Set.Icc (-1 : ℝ) 1))

/-- Nodes are valid: strictly increasing and in [-1, 1]. (`StrictMono`
    canonicalises the ordering; the Lebesgue constant is invariant under
    permutations of the nodes.) -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- Nodes are canonical: valid, with the endpoints -1 and 1 among the nodes
    (so, by strict monotonicity, `nodes 0 = -1` and `nodes (n-1) = 1`).
    This is the normalisation in which the Bernstein–Erdős uniqueness and
    equioscillation theorems hold; see the module docstring. -/
def CanonicalNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  ValidNodes nodes ∧ (∃ i, nodes i = -1) ∧ (∃ i, nodes i = 1)

/-- The boundary sequence for the (n+1)-interval equioscillation property:
    -1, then the n nodes in order, then 1, giving n + 2 points partitioning
    [-1, 1] into n + 1 subintervals.

    Degeneracy note: when `nodes 0 = -1` (resp. `nodes (n-1) = 1`) the outer
    subinterval [b_0, b_1] (resp. [b_n, b_{n+1}]) is a singleton, on which the
    local maximum of the Lebesgue function is L(±1) = 1. This is why canonical
    minimisers do not satisfy `HasEquioscillation` for n ≥ 3. -/
def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The (n+1)-interval equioscillation property of the source page: the local
    maximum of the Lebesgue function is the same on each of the n + 1
    subintervals [b_i, b_{i+1}] of the partition of [-1,1] by the nodes
    together with x_0 = -1 and x_{n+1} = 1.

    This is Erdős's formulation for free nodes; configurations with this
    property exist ([KiCh76], see `erdos_problem_1129.variants.kilgore_cheney`)
    and are minimisers, but not every minimiser has it (see the module
    docstring), so it does not appear in the corrected main theorem. -/
def HasEquioscillation {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin (n + 1),
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
               (boundary nodes ⟨i.val + 1, by omega⟩))) =
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (boundary nodes ⟨j.val, by omega⟩)
               (boundary nodes ⟨j.val + 1, by omega⟩)))

/-- The equioscillation property in the canonical normalisation: the local
    maximum of the Lebesgue function is the same on each of the n - 1
    intervals [x_i, x_{i+1}] between consecutive nodes. (For canonical nodes
    these intervals cover [-1, 1], so the common value is Λ itself.) -/
def CanonicalEquioscillation {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin (n - 1),
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (nodes ⟨i.val, by omega⟩) (nodes ⟨i.val + 1, by omega⟩))) =
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (nodes ⟨j.val, by omega⟩) (nodes ⟨j.val + 1, by omega⟩)))

/--
Erdős Problem #1129 (PROVED — Kilgore–Cheney [KiCh76], Kilgore [Ki77], and
de Boor–Pinkus [dBPi78]):

For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k}(x-xᵢ)/(x_k-xᵢ) be the
Lagrange basis polynomials and Λ = max_{x∈[-1,1]} ∑_k |l_k(x)| the Lebesgue
constant. Erdős and Bernstein conjectured that the minimising nodes are
unique and characterised by equioscillation of the Lebesgue function. In the
canonical normalisation x₁ = -1, xₙ = 1, in which these conjectures are true
and were proved: there is a canonical configuration `opt` that minimises Λ
over *all* valid configurations (the minimum value is insensitive to the
normalisation, by affine invariance of the inter-node local maxima), it is
the unique minimiser *among canonical configurations* (de Boor–Pinkus
[dBPi78]), and it equioscillates over the n - 1 intervals between
consecutive nodes (Kilgore [Ki77]: Λ is minimised only when all the local
maxima are equal).

Uniqueness over all valid configurations — asserted by the first-pass
version of this theorem — is false for n ≥ 3; see the module docstring for
the counterexample continuum.

NOTE: corrected by the fable review of 2026-08-14; not compile-verified.
-/
theorem erdos_problem_1129 (n : ℕ) (hn : 2 ≤ n) :
    ∃ opt : Fin n → ℝ, CanonicalNodes opt ∧
      -- opt achieves the minimum Lebesgue constant over all valid nodes
      (∀ nodes : Fin n → ℝ, ValidNodes nodes →
        lebesgueConstant opt ≤ lebesgueConstant nodes) ∧
      -- the minimiser is unique among canonical configurations
      (∀ nodes : Fin n → ℝ, CanonicalNodes nodes →
        lebesgueConstant nodes = lebesgueConstant opt → nodes = opt) ∧
      -- the minimiser equioscillates between consecutive nodes
      CanonicalEquioscillation opt :=
  sorry

/--
Kilgore–Cheney [KiCh76] (page remark, SOLVED): there exist nodes for which
all n + 1 local maxima λ₀, ..., λₙ of Erdős's formulation (outer intervals
included) are equal. Such configurations are interior — both outer intervals
must be nondegenerate — and are obtained by shrinking the canonical optimum
until the outer maxima rise to the common interior value.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1129.variants.kilgore_cheney (n : ℕ) (hn : 2 ≤ n) :
    ∃ nodes : Fin n → ℝ, ValidNodes nodes ∧ HasEquioscillation nodes :=
  sorry

/--
Symmetry of the canonical minimiser (page remark, SOLVED): the unique
minimising canonical set of nodes is symmetric around 0, i.e. any canonical
minimiser satisfies x_{n+1-i} = -x_i (0-indexed: `opt (n-1-i) = -opt i`).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1129.variants.symmetric (n : ℕ) (hn : 2 ≤ n)
    (opt : Fin n → ℝ) (hopt : CanonicalNodes opt)
    (hmin : ∀ nodes : Fin n → ℝ, CanonicalNodes nodes →
      lebesgueConstant opt ≤ lebesgueConstant nodes) :
    ∀ i : Fin n, opt ⟨n - 1 - i.val, by omega⟩ = - opt i :=
  sorry

/--
The case n = 2 (page remark, SOLVED): the minimising points are -1, 1, with
Λ = 1 (the Lebesgue function of the nodes -1, 1 is identically 1 on [-1,1],
and every valid configuration has Λ ≥ 1 since L equals 1 at each node).
Here the minimality holds over all valid configurations, and for n = 2 the
minimiser is in fact unique even in the free-node setting.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1129.variants.two_nodes :
    lebesgueConstant (fun i : Fin 2 => 2 * (i.val : ℝ) - 1) = 1 ∧
    ∀ nodes : Fin 2 → ℝ, ValidNodes nodes →
      1 ≤ lebesgueConstant nodes :=
  sorry

/--
The case n = 3, Bernstein [Be31] (page remark, SOLVED): the minimising
canonical points are -1, 0, 1, with Λ = 5/4. The lower bound 5/4 holds over
all valid configurations (not only canonical ones) by affine invariance of
the inter-node local maxima — though for n = 3 the free-node minimiser is
not unique (see the module docstring).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1129.variants.three_nodes :
    lebesgueConstant (fun i : Fin 3 => (i.val : ℝ) - 1) = 5 / 4 ∧
    ∀ nodes : Fin 3 → ℝ, ValidNodes nodes →
      5 / 4 ≤ lebesgueConstant nodes :=
  sorry

end Erdos1129
