import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #745

Describe the size of the second largest component of the random graph on n
vertices, where each edge is included independently with probability 1/n.

Erdős believed that almost surely the second largest component has size ≪ log n.
This is true, as proved by Komlós, Sulyok, and Szemerédi [KSS80].
-/

/-- The simple graph on Fin n determined by a Boolean edge configuration. -/
def toGraph745 {n : ℕ} (ec : Fin n → Fin n → Bool) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ec (min u v) (max u v) = true
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, by rwa [min_comm, max_comm]⟩
  loopless := ⟨fun v ⟨h, _⟩ => h rfl⟩

/-- The number of edges in a Boolean edge configuration on Fin n
    (counting only pairs i < j to avoid double-counting). -/
def edgeCount745 {n : ℕ} (ec : Fin n → Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ ec p.1 p.2 = true)).card

/-- The probability weight of a specific edge configuration under the
    Erdős–Rényi model G(n, 1/n): each edge is included independently
    with probability 1/n. -/
noncomputable def gnpWeight745 (n : ℕ) (ec : Fin n → Fin n → Bool) : ℝ :=
  (1 / (n : ℝ)) ^ edgeCount745 ec *
  (1 - 1 / (n : ℝ)) ^ (n.choose 2 - edgeCount745 ec)

/-- The G(n, 1/n)-probability of a graph property P: the sum of weights
    over all edge configurations whose graph satisfies P. -/
noncomputable def gnpProb745 (n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Finset.univ.filter (fun ec : Fin n → Fin n → Bool =>
    P (toGraph745 ec))).sum (gnpWeight745 n)

/-- The size of the connected component containing vertex v in graph G. -/
noncomputable def componentSize745 {n : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun w : Fin n => G.Reachable v w)).card

/-- The size of the second largest connected component of G on Fin n.
    Defined as the smallest k such that at most one connected component
    has more than k vertices; equivalently, any two vertices whose
    components both exceed size k must be in the same component. -/
noncomputable def secondLargestComponent745 {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k : ℕ | ∀ u v : Fin n,
    componentSize745 G u > k → componentSize745 G v > k → G.Reachable u v}

/--
Erdős Problem #745 [Er81]:

In the Erdős–Rényi random graph G(n, 1/n), the second largest connected
component almost surely has size O(log n).

Formally: there exists a constant C > 0 such that for every ε > 0 there
exists n₀ such that for all n ≥ n₀, the G(n, 1/n)-probability that the
second largest component has size at most C · log n is at least 1 − ε.

Proved by Komlós, Sulyok, and Szemerédi [KSS80].
-/
theorem erdos_problem_745 :
    ∃ C : ℝ, C > 0 ∧
    ∀ ε : ℝ, ε > 0 →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      gnpProb745 n (fun G =>
        (secondLargestComponent745 G : ℝ) ≤ C * Real.log (n : ℝ)) ≥ 1 - ε :=
  sorry

end
