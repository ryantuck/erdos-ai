import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Real Finset Topology

noncomputable section

/-!
# Erdős Problem #156

Does there exist a maximal Sidon set $A \subset \{1, \ldots, N\}$ of size $O(N^{1/3})$?

A question of Erdős, Sárközy, and Sós [ESS94]. It is easy to prove that the greedy
construction of a maximal Sidon set in $\{1, \ldots, N\}$ has size $\gg N^{1/3}$.
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$, but
whether $O(N^{1/3})$ is achievable remains open.
-/

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A Sidon set A ⊆ {0, ..., N-1} is maximal (in {0, ..., N-1}) if no element of
    {0, ..., N-1} \ A can be added to A while preserving the Sidon property. -/
def IsMaximalSidonSet (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range N ∧
  IsSidonSet A ∧
  ∀ n ∈ Finset.range N, n ∉ A → ¬IsSidonSet (insert n A)

/--
Erdős–Sárközy–Sós Conjecture (Problem #156) [ESS94]:

Does there exist a maximal Sidon set $A \subset \{1, \ldots, N\}$ of size $O(N^{1/3})$?

This is the conjecture that the answer is YES.

The greedy algorithm produces a maximal Sidon set of size $\gg N^{1/3}$ (this is known).
Ruzsa [Ru98b] constructed a maximal Sidon set of size $\ll (N \log N)^{1/3}$, which is
close but does not reach $O(N^{1/3})$.

Formalized as: there exists a constant $C > 0$ such that for all sufficiently large $N$,
there exists a maximal Sidon set $A \subseteq \{0, \ldots, N-1\}$ with
$|A| \leq C \cdot N^{1/3}$.
-/
theorem erdos_problem_156 :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ A : Finset ℕ, IsMaximalSidonSet N A ∧
          (A.card : ℝ) ≤ C * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  sorry

end
