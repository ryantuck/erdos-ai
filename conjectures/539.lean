import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Real

noncomputable section

/-!
# Erdos Problem #539

Let $h(n)$ be such that, for any set $A \subseteq \mathbb{N}$ of size $n$, the set
$$\left\{ \frac{a}{\gcd(a,b)} : a, b \in A \right\}$$
has size at least $h(n)$. Estimate $h(n)$.

Erdos and Szemeredi proved that $n^{1/2} \ll h(n) \ll n^{1-c}$ for some constant
$c > 0$. The upper bound has been improved to $h(n) \ll n^{2/3}$ by Freiman and Lev.
-/

/-- The set of gcd-quotients `{a / gcd(a, b) : a, b in A}` for a finite set `A` of
natural numbers. -/
def gcdQuotientSet (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image (fun p => p.1 / Nat.gcd p.1 p.2)

/--
**Erdos Problem #539** (Lower bound, Erdos-Szemeredi):

There exists a constant `C > 0` such that for any finite set `A` of positive integers
of size `n`, the set `{a / gcd(a, b) : a, b in A}` has size at least `C * n^(1/2)`.
-/
theorem erdos_problem_539_lower :
    ∃ C : ℝ, 0 < C ∧
    ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) →
      C * ((A.card : ℝ) ^ ((1 : ℝ) / 2)) ≤ ((gcdQuotientSet A).card : ℝ) :=
  sorry

/--
**Erdos Problem #539** (Upper bound, Freiman-Lev):

There exists a constant `C > 0` such that for all sufficiently large `n`, there exists
a finite set `A` of positive integers of size `n` whose gcd-quotient set has size at most
`C * n^(2/3)`.
-/
theorem erdos_problem_539_upper :
    ∃ C : ℝ, 0 < C ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ A : Finset ℕ, (∀ a ∈ A, 0 < a) ∧ A.card = n ∧
        ((gcdQuotientSet A).card : ℝ) ≤ C * ((n : ℝ) ^ ((2 : ℝ) / 3)) :=
  sorry

end
