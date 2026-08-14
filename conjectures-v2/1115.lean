import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Erdős Problem #1115

Source: https://www.erdosproblems.com/1115 (page last edited 29 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "Let $f(z)$ be an entire function of finite order, and let
$\Gamma$ be a rectifiable path on which $f(z)\to \infty$. Let $\ell(r)$ be the
length of $\Gamma$ in the disc $\lvert z\rvert<r$.

Find a path for which $\ell(r)$ grows as slowly as possible, and estimate
$\ell(r)$ in terms of $M(r)=\max_{\lvert z\rvert=r}\lvert f(z)\rvert$.

In particular, can such a path $\Gamma$ be found for which $\ell(r)\ll r$?"

Status: SOLVED (banner tooltip: "This has been resolved in some other way than
a proof or disproof."). Tag: analysis.

Remarks from the page:

* "A problem originally due to Hayman [Ha60], according to [GoEr79], although
  (confusingly) in the book [Ha74] by Hayman it is attributed to Erdős, as
  Problem 2.41."
* "Hayman [Ha60b] proved that if $\log M(r) \ll (\log r)^2$ then there exists
  a path $\Gamma$ on which $f(z)\to \infty$ and $\ell(r)=r$." (Not formalized
  here: it needs the maximum modulus $M(r)$ and $\log$, machinery not present
  in this file; see fable-review/1115.md.)
* "Disproved by Gol'dberg and Eremenko [GoEr79] who proved that for any
  function $\phi(r)$ which $\to \infty$ as $r\to \infty$ there is an entire
  function $f$ such that $\log M(r) \ll \phi(r)(\log r)^2$ and there is no
  path $\Gamma$ on which $f(z)\to \infty$ and $\ell(r) \ll r$. They also
  construct such functions of any prescribed finite order in $[0,\infty)$."
  (The quantitative $\log M$ refinement likewise needs $M(r)$ and is not
  formalized; the prescribed-order clause is formalized as a variant below.)

Encoding notes. Only the formalizable yes/no core ("can such a path always be
found with $\ell(r)\ll r$?" — answered NO) is stated; the soft "find a path /
estimate $\ell(r)$ in terms of $M(r)$" framing is not a single proposition and
is recorded here instead. The problem is solved in the negative direction and
this raw corpus has no answer-elaborator, so the theorem is the direct
assertion of the Gol'dberg–Eremenko refutation. The first-pass statement was
trivially true: it asserted only `∀ γ, TendsToInfinityAlong f γ → …`, which
any constant function satisfies vacuously (a constant is entire of finite
order and tends to infinity along no path). v2 adds the conjunct
`∃ γ, TendsToInfinityAlong f γ`, matching the problem's setup ("let $\Gamma$
be a rectifiable path on which $f(z)\to\infty$" presupposes such paths exist);
for the Gol'dberg–Eremenko function the conjunct holds by Iversen's theorem
($\infty$ is an asymptotic value of every nonconstant entire function, along
an asymptotic path that may be taken polygonal, hence arc-length
parameterizable). `pathLengthInDisk` measures the closed disc
$\lvert z\rvert\le r$ where the source writes the open disc
$\lvert z\rvert<r$; since $\ell$ is monotone in $r$ and
$\ell_{\mathrm{closed}}(r)\le\ell_{\mathrm{open}}(r+1)$, the two readings of
"$\ell(r) = O(r)$" agree, so nothing is changed. An `ArcLengthPath` is defined
on all of ℝ, but only $t \ge 0$ is constrained or measured — the negative-time
part is inert, and any path on $[0,\infty)$ extends (e.g. constantly) to ℝ.

References (authors, titles, journals, years, and pages recovered from the
site's `/latex/1115` bibliography via the session logs; volume numbers were
not in the recovered data and are omitted rather than invented):

[GoEr79] Gol'dberg, A. A. and Eremenko, A. È., _Asymptotic curves of entire
functions of finite order_. Mat. Sb. (N.S.) (1979), 555–581, 647.

[Ha60] Hayman, W. K., _Defective values and asymptotic paths_. Matematika
(1960), 21–27.

[Ha60b] Hayman, W. K., _Slowly growing integral and subharmonic functions_.
Comment. Math. Helv. (1960), 75–84.

[Ha74] Hayman, W. K., _Research problems in function theory: new problems_
(1974), 155–180.

Additional thanks to: Alfaiz. Formalised statement in external databases: No
(as of the archived capture). No related OEIS sequences are listed.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory

namespace Erdos1115

/-- An entire function: differentiable everywhere on ℂ. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- An entire function has finite order: there exists ρ ≥ 0 such that
    |f(z)| ≤ exp(C · |z|^ρ) for all sufficiently large |z|. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ (C R : ℝ), 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ ρ)

/-- `f` has order exactly `ρ`: for every ε > 0, eventually
    ‖f z‖ ≤ exp(‖z‖ ^ (ρ + ε)), but it is *not* the case that eventually
    ‖f z‖ ≤ exp(‖z‖ ^ (ρ - ε)). For nonconstant entire `f` (the only case in
    which it is used below) this is the standard characterization of
    limsup_{r → ∞} (log log M(r)) / (log r) = ρ. -/
def HasOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (‖z‖ ^ (ρ + ε))) ∧
  ∀ ε : ℝ, 0 < ε → ¬∃ R : ℝ, 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (‖z‖ ^ (ρ - ε))

/-- An arc-length parameterized rectifiable path in ℂ going to infinity.
    The parameter t represents arc length from the start. -/
structure ArcLengthPath where
  toFun : ℝ → ℂ
  continuous' : Continuous toFun
  /-- The path goes to infinity: |γ(t)| → ∞ as t → ∞. -/
  tendsToInfinity : Tendsto (fun t => ‖toFun t‖) atTop atTop
  /-- Parameterized by arc length: the variation on [0, T] equals T. -/
  isArcLength : ∀ T : ℝ, 0 ≤ T → eVariationOn toFun (Icc 0 T) = ENNReal.ofReal T

/-- f(z) → ∞ along a path γ. -/
def TendsToInfinityAlong (f : ℂ → ℂ) (γ : ArcLengthPath) : Prop :=
  Tendsto (fun t => ‖f (γ.toFun t)‖) atTop atTop

/-- The arc length of an arc-length parameterized path γ inside the closed disk
    of radius r. For arc-length parameterization, this equals the Lebesgue measure
    of {t ≥ 0 : |γ(t)| ≤ r}. -/
noncomputable def pathLengthInDisk (γ : ArcLengthPath) (r : ℝ) : ℝ :=
  (volume (({t : ℝ | 0 ≤ t ∧ ‖γ.toFun t‖ ≤ r}) : Set ℝ)).toReal

/--
Erdős Problem #1115 (SOLVED — disproved by Gol'dberg and Eremenko [GoEr79];
originally due to Hayman [Ha60] according to [GoEr79], though attributed to
Erdős as Problem 2.41 in Hayman's book [Ha74]):

Let f(z) be an entire function of finite order, and let Γ be a rectifiable path
on which f(z) → ∞. Let ℓ(r) be the length of Γ in the disc |z| < r.

Can such a path Γ always be found with ℓ(r) ≪ r?

Disproved: Gol'dberg and Eremenko showed that for any φ(r) → ∞ there is an
entire function f with log M(r) ≪ φ(r)(log r)² such that there is no path Γ
on which f(z) → ∞ and ℓ(r) ≪ r. They also construct such functions of any
prescribed finite order in [0, ∞).

Formally (the true, negative direction, as a direct assertion): there exists an
entire function f of finite order such that arc-length parameterized paths to
infinity on which f → ∞ *do exist*, but no such path has ℓ(r) = O(r). The
existence conjunct rules out the degenerate constant witnesses that satisfy the
universal clause vacuously; for the Gol'dberg–Eremenko function it holds by
Iversen's theorem.

NOTE: the added existence conjunct is from this review pass and is not
compile-verified.
-/
theorem erdos_problem_1115 :
    ∃ f : ℂ → ℂ, IsEntire f ∧ HasFiniteOrder f ∧
      (∃ γ : ArcLengthPath, TendsToInfinityAlong f γ) ∧
      ∀ γ : ArcLengthPath, TendsToInfinityAlong f γ →
        ¬∃ (C R : ℝ), ∀ r : ℝ, R ≤ r → pathLengthInDisk γ r ≤ C * r :=
  sorry

/--
Page-confirmed strengthening (SOLVED, Gol'dberg and Eremenko [GoEr79]): "They
also construct such functions of any prescribed finite order in $[0,\infty)$."
For every ρ ≥ 0 there is an entire function of order exactly ρ that admits
arc-length parameterized paths to infinity on which it tends to infinity, yet
no such path has ℓ(r) = O(r).

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1115.variants.prescribed_order (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ f : ℂ → ℂ, IsEntire f ∧ HasOrder f ρ ∧
      (∃ γ : ArcLengthPath, TendsToInfinityAlong f γ) ∧
      ∀ γ : ArcLengthPath, TendsToInfinityAlong f γ →
        ¬∃ (C R : ℝ), ∀ r : ℝ, R ≤ r → pathLengthInDisk γ r ≤ C * r :=
  sorry

end Erdos1115
