import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #576

Let $Q_k$ be the $k$-dimensional hypercube graph (so that $Q_k$ has $2^k$ vertices
and $k \cdot 2^{k-1}$ edges). Determine the behaviour of $\mathrm{ex}(n; Q_k)$.

Erdős and Simonovits proved that
  $(1/2 + o(1))n^{3/2} \leq \mathrm{ex}(n; Q_3) \ll n^{8/5}$.

Erdős asked whether $\mathrm{ex}(n; Q_3) \asymp n^{8/5}$.

References: [Er64c], [ErSi70,p.378], [Er74c,p.78], [Er75], [Er81], [Er93,p.334]
-/

/-- The k-dimensional hypercube graph Q_k: vertices are functions Fin k → Bool,
    and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph576 (k : ℕ) : SimpleGraph (Fin k → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

/-- An injective graph homomorphism from H to G: G contains a copy of H as a subgraph. -/
def containsSubgraph576 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber576 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph576 F H ∧ F.edgeFinset.card = m}

/--
Erdős Conjecture (Problem #576) [Er64c], [ErSi70], [Er74c], [Er81], [Er93]:

Let Q_3 be the 3-dimensional hypercube graph. Erdős and Simonovits proved that
  (1/2 + o(1)) · n^{3/2} ≤ ex(n; Q_3) ≪ n^{8/5}.

Erdős conjectured that ex(n; Q_3) ≍ n^{8/5}, i.e., there exist constants
c, C > 0 such that for all sufficiently large n,
  c · n^{8/5} ≤ ex(n; Q_3) ≤ C · n^{8/5}.
-/
theorem erdos_problem_576 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ^ ((8 : ℝ) / 5) ≤ (turanNumber576 (hypercubeGraph576 3) n : ℝ) ∧
      (turanNumber576 (hypercubeGraph576 3) n : ℝ) ≤ C * (n : ℝ) ^ ((8 : ℝ) / 5) :=
  sorry

end
