import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #746

Is it true that, almost surely, a random graph on n vertices with
≥ (1/2 + ε)n log n edges is Hamiltonian?

A conjecture of Erdős and Rényi [ErRe66]. This was proved: Pósa [Po76]
showed this with Cn log n edges for some large C, Korshunov [Ko77] improved
the threshold, and Komlós and Szemerédi [KoSz83] proved the sharp result
that with (1/2)n log n + (1/2)n log log n + cn edges the probability of
being Hamiltonian tends to e^{-e^{-2c}}.

https://www.erdosproblems.com/746

Tags: graph theory
-/

/-- The simple graph on Fin n determined by a Boolean edge configuration. -/
def toGraph746 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/-- The number of edges in a Boolean edge configuration on Fin n
    (counting only pairs i < j to avoid double-counting). -/
def edgeCount746 {n : ℕ} (ec : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ ec p.1 p.2 = true)).card

/-- The set of all edge configurations on Fin n with exactly m edges. -/
def graphsWithEdges746 (n m : ℕ) : Finset (Fin n → Fin n → Bool) :=
  Finset.univ.filter (fun ec => edgeCount746 ec = m)

/-- The fraction of graphs on Fin n with exactly m edges that satisfy
    property P (the G(n,m) probability of P). Returns 0 if there are
    no graphs with exactly m edges. -/
noncomputable def gnmFraction746 (n m : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  ((graphsWithEdges746 n m).filter (fun ec => P (toGraph746 ec))).card /
  ((graphsWithEdges746 n m).card : ℝ)

/--
Erdős Problem #746 [Er71, Er81, Er82e]:

For every ε > 0, almost surely a random graph on n vertices with at least
(1/2 + ε) · n · log n edges is Hamiltonian.

Formally: for every ε > 0 and δ > 0, there exists n₀ such that for all
n ≥ n₀ and all m with (1/2 + ε) · n · log n ≤ m ≤ C(n,2), the
G(n,m)-probability that the graph is Hamiltonian is at least 1 − δ.

Proved by Komlós and Szemerédi [KoSz83].
-/
theorem erdos_problem_746 :
    ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∀ m : ℕ, (m : ℝ) ≥ (1/2 + ε) * (n : ℝ) * Real.log (n : ℝ) →
        m ≤ n.choose 2 →
        gnmFraction746 n m (fun G => G.IsHamiltonian) ≥ 1 - δ :=
  sorry

end
