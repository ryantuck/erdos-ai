import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Ring.Real

open Finset Filter Nat BigOperators Classical

noncomputable section

/-!
# Erdős Problem #235

Let Nₖ = 2·3·…·pₖ (the k-th primorial) and let a₁ < a₂ < ⋯ < a_{φ(Nₖ)}
be the integers less than Nₖ coprime to Nₖ. Then for any c ≥ 0, the limit

  lim_{k→∞} #{i : aᵢ - aᵢ₋₁ ≤ c·Nₖ/φ(Nₖ)} / φ(Nₖ)

exists and defines a continuous function of c.

Proved by Hooley [Ho65], who showed that the limiting distribution is
exponential: f(c) = 1 - e^{-c}.
-/

/-- The k-th primorial: product of the first k primes (p₁ · p₂ · … · pₖ). -/
def primorial (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, nth Nat.Prime i

/-- The sorted list of natural numbers less than n that are coprime to n. -/
def sortedCoprimes (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun a => Nat.Coprime a n)).sort (· ≤ ·)

/-- Count consecutive gaps ≤ threshold in a sorted list of naturals. -/
def countSmallGaps : List ℕ → ℝ → ℕ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: rest, threshold =>
    (if ((b : ℝ) - (a : ℝ)) ≤ threshold then 1 else 0) + countSmallGaps (b :: rest) threshold

/-- The fraction of consecutive gaps among reduced residues mod Nₖ
    that are at most c · Nₖ / φ(Nₖ). -/
def gapFraction (k : ℕ) (c : ℝ) : ℝ :=
  let Nk := primorial k
  let residues := sortedCoprimes Nk
  let threshold := c * (Nk : ℝ) / (Nat.totient Nk : ℝ)
  (countSmallGaps residues threshold : ℝ) / (Nat.totient Nk : ℝ)

/--
Erdős Problem #235 [Er55c] (proved by Hooley [Ho65]):

Let Nₖ = 2·3·…·pₖ (the k-th primorial) and let a₁ < a₂ < ⋯ < a_{φ(Nₖ)}
be the integers less than Nₖ coprime to Nₖ. Then for any c ≥ 0, the limit

  lim_{k→∞} #{i : aᵢ - aᵢ₋₁ ≤ c·Nₖ/φ(Nₖ)} / φ(Nₖ)

exists and defines a continuous function of c.

Hooley proved that the limiting distribution is exponential: f(c) = 1 - e^{-c}.
-/
theorem erdos235 :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ c : ℝ, 0 ≤ c →
        Tendsto (fun k => gapFraction k c) atTop (nhds (f c)) :=
  sorry

end
