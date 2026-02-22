import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #1080

Let $G$ be a bipartite graph on $n$ vertices such that one part has
$\lfloor n^{2/3}\rfloor$ vertices. Is there a constant $c > 0$ such that
if $G$ has at least $cn$ edges then $G$ must contain a $C_6$?

The answer is no, as shown by De Caen and Székely [DeSz92]. They prove that
$f(n,\lfloor n^{2/3}\rfloor) \gg n^{58/57+o(1)}$ where $f(n,m)$ is the
maximum number of edges in a bipartite graph with parts of sizes $n$ and $m$
containing no $C_4$ or $C_6$. This lower bound was improved to
$\gg n^{16/15+o(1)}$ by Lazebnik, Ustimenko, and Woldar [LUW94].
-/

/-- A simple graph contains a cycle of length `k` if there exists an injective map
    `f : Fin k → V` such that `f i` is adjacent to `f ((i+1) mod k)` for every `i`. -/
def SimpleGraph.ContainsCycleOfLength {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (f : Fin k → V), Function.Injective f ∧
    ∀ i : Fin k, G.Adj (f i) (f ⟨(i.val + 1) % k, Nat.mod_lt _ (by have := i.isLt; omega)⟩)

/-- A bipartite graph on `Fin n` with the first `a` vertices forming one part:
    all edges go between vertices with index `< a` and vertices with index `≥ a`. -/
def SimpleGraph.IsBipartiteWithFirstPart {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ) : Prop :=
  ∀ u v : Fin n, G.Adj u v → (u.val < a ∧ v.val ≥ a) ∨ (u.val ≥ a ∧ v.val < a)

/--
Erdős Problem #1080 [Er75][Er79g] (Disproved):

There is no constant $c > 0$ such that every bipartite graph on $n$ vertices
with one part of size $\lfloor n^{2/3}\rfloor$ and at least $cn$ edges must
contain a $C_6$. Disproved by De Caen and Székely [DeSz92].
-/
theorem erdos_problem_1080 (c : ℝ) (hc : c > 0) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.IsBipartiteWithFirstPart (Nat.floor ((n : ℝ) ^ ((2 : ℝ) / 3))) ∧
    (G.edgeFinset.card : ℝ) ≥ c * ↑n ∧
    ¬G.ContainsCycleOfLength 6 :=
  sorry

end
