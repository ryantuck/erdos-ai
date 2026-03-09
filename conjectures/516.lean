import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.LiminfLimsup

open Complex Filter Topology

noncomputable section

/--
The maximum modulus of f on the circle of radius r: M(r) = max_{|z|=r} |f(z)|.
-/
def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup ((fun z => ‖f z‖) '' {z : ℂ | ‖z‖ = r})

/--
The minimum modulus of f on the circle of radius r: m(r) = min_{|z|=r} |f(z)|.
-/
def minModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sInf ((fun z => ‖f z‖) '' {z : ℂ | ‖z‖ = r})

/--
An entire function f has finite order if there exists ρ > 0 such that
M(r) ≤ C · exp(r^ρ) for all sufficiently large r.
-/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ᶠ r in atTop, maxModulus f r ≤ C * Real.exp (r ^ ρ)

/--
Erdős Problem #516 [Er61, p.249]:

Let f(z) = ∑_{k≥1} aₖ z^{nₖ} be an entire function of finite order such that
lim nₖ/k = ∞. Let M(r) = max_{|z|=r} |f(z)| and m(r) = min_{|z|=r} |f(z)|.
Is it true that limsup_{r→∞} (log m(r) / log M(r)) = 1?

A problem of Pólya. This was solved in the affirmative by Fuchs [Fu63], who
proved that for any ε > 0, log m(r) > (1-ε) log M(r) holds outside a set of
logarithmic density 0.
-/
theorem erdos_problem_516
    (n : ℕ → ℕ) (a : ℕ → ℂ) (f : ℂ → ℂ)
    (hn_strict : StrictMono n)
    (hf_entire : Differentiable ℂ f)
    (hf_order : HasFiniteOrder f)
    (hf_series : ∀ z : ℂ, HasSum (fun k => a k * z ^ n k) (f z))
    (hn_lacunary : Tendsto (fun k => (n k : ℝ) / (k : ℝ)) atTop atTop) :
    Filter.limsup (fun r : ℝ =>
      Real.log (minModulus f r) / Real.log (maxModulus f r)) atTop = 1 :=
  sorry
