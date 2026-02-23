import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.SetTheory.Cardinal.Continuum

noncomputable section
open Cardinal Classical Set

namespace Erdos1119

/--
Erdős Problem #1119 (Independent of ZFC) [Ha74]:

Let 𝔪 be an infinite cardinal with ℵ₀ < 𝔪 < 𝔠 = 2^{ℵ₀}. Let {f_α} be a family of
entire functions such that, for every z₀ ∈ ℂ, the set {f_α(z₀)} of values has at most
𝔪 distinct elements. Must the family of distinct functions have cardinality at most 𝔪?

This generalizes Wetzel's problem. Erdős proved that for the countable case
(ℵ₀ values), the answer is yes if 𝔠 > ℵ₁ and no if 𝔠 = ℵ₁.
Kumar–Shelah [KuSh17] showed the answer can be yes (with 𝔪 = ℵ₁, 𝔠 = ℵ₂),
while Schilhan–Weinert [ScWe24] showed it can be no.
-/
theorem erdos_problem_1119 (𝔪 : Cardinal) (h1 : ℵ₀ < 𝔪) (h2 : 𝔪 < Cardinal.continuum)
    (ι : Type) (f : ι → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i))
    (hval : ∀ z : ℂ, Cardinal.mk ↥(range (fun i => f i z)) ≤ 𝔪) :
    Cardinal.mk ↥(range f) ≤ 𝔪 :=
  sorry

end Erdos1119
