import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

/--
An n-uniform hypergraph is a finite collection of edges where each edge
has exactly n vertices.
-/
def IsNUniform (H : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ e ∈ H, e.card = n

/--
A hypergraph has Property B (is 2-colorable) if there exists a 2-coloring
of the vertex set such that no edge is monochromatic, i.e., every edge
contains vertices of both colors.
-/
def HasPropertyB (H : Finset (Finset ℕ)) : Prop :=
  ∃ f : ℕ → Bool, ∀ e ∈ H, (∃ x ∈ e, f x = true) ∧ (∃ x ∈ e, f x = false)

/--
Erdős Problem #901 (Erdős-Lovász Conjecture), lower bound:
Let m(n) be minimal such that there is an n-uniform hypergraph with m(n) edges
that does not have Property B. Erdős and Lovász conjecture that m(n) is of
order n · 2^n.

Lower bound: there exists c > 0 such that for all sufficiently large n,
every n-uniform hypergraph without Property B has at least c · n · 2^n edges.
-/
theorem erdos_problem_901_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ (H : Finset (Finset ℕ)),
        IsNUniform H n → ¬HasPropertyB H →
        (H.card : ℝ) ≥ c * ↑n * (2 : ℝ) ^ n :=
  sorry

/--
Erdős Problem #901 (Erdős-Lovász Conjecture), upper bound:
There exists c > 0 such that for all sufficiently large n, there exists
an n-uniform hypergraph without Property B with at most c · n · 2^n edges.
-/
theorem erdos_problem_901_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ (H : Finset (Finset ℕ)),
        IsNUniform H n ∧ ¬HasPropertyB H ∧
        (H.card : ℝ) ≤ c * ↑n * (2 : ℝ) ^ n :=
  sorry
