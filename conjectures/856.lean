import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

noncomputable section

open Finset Real

/-!
# Erdős Problem #856

Let $k ≥ 3$ and $f_k(N)$ be the maximum value of $∑_{n ∈ A} 1/n$, where $A$
ranges over all subsets of $\{1, …, N\}$ which contain no subset of size $k$
with the same pairwise least common multiple.

Estimate $f_k(N)$.

Erdős [Er70] proved that $f_k(N) ≪ \log N / \log(\log N)$.

Tang and Zhang [TaZh25b] proved bounds of the form
  $(\log N)^{b_k - o(1)} ≤ f_k(N) ≤ (\log N)^{c_k + o(1)}$
for constants $0 < b_k ≤ c_k ≤ 1$, and in particular
  $(\log N)^{0.438} ≤ f_3(N) ≤ (\log N)^{0.889}$ for all large $N$.

https://www.erdosproblems.com/856

Tags: number theory
-/

/-- A Finset of natural numbers has no k-element subset where all pairwise
    LCMs are equal. That is, there is no S ⊆ A with |S| = k and a value L
    such that lcm(a, b) = L for all distinct a, b ∈ S. -/
def NoPairwiseLcmClique856 (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ A → S.card = k →
    ¬∃ L : ℕ, ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Nat.lcm a b = L

/-- f_k(N): the supremum of ∑_{n ∈ A} 1/n over subsets A ⊆ {1, …, N}
    with no k-element subset having all pairwise LCMs equal. -/
noncomputable def erdos856_fk (k N : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
    NoPairwiseLcmClique856 A k ∧
    x = ∑ n ∈ A, (1 : ℝ) / (n : ℝ)}

/--
**Erdős Problem #856** — Upper bound [Er70]:

For every k ≥ 3, there exists C > 0 such that for all sufficiently large N,
  f_k(N) ≤ C · log(N) / log(log(N)).
-/
theorem erdos_problem_856_upper (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      erdos856_fk k N ≤ C * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
  sorry

/--
**Erdős Problem #856** — Tang-Zhang lower bound [TaZh25b]:

For every k ≥ 3, there exist constants b with 0 < b ≤ 1 and C > 0 such that
for all sufficiently large N,
  f_k(N) ≥ C · (log N)^b.
-/
theorem erdos_problem_856_tang_zhang_lower (k : ℕ) (hk : k ≥ 3) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      erdos856_fk k N ≥ C * (Real.log (N : ℝ)) ^ b :=
  sorry

/--
**Erdős Problem #856** — Tang-Zhang upper bound [TaZh25b]:

For every k ≥ 3, there exist constants c with 0 < c ≤ 1 and C > 0 such that
for all sufficiently large N,
  f_k(N) ≤ C · (log N)^c.

The exponents c_k are < 1 (improving over the trivial bound) if and only if
the sunflower conjecture [857] holds for k-sunflowers.
-/
theorem erdos_problem_856_tang_zhang_upper (k : ℕ) (hk : k ≥ 3) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      erdos856_fk k N ≤ C * (Real.log (N : ℝ)) ^ c :=
  sorry

end
