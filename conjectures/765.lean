import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #765

Give an asymptotic formula for ex(n; C₄).

Erdős and Klein proved ex(n; C₄) ≍ n^{3/2}. Reiman proved
  1/(2√2) ≤ lim ex(n; C₄)/n^{3/2} ≤ 1/2.
Erdős–Rényi and independently Brown showed that for n = q² + q + 1 with q a
prime power, ex(n; C₄) ≥ q(q+1)²/2, which together with Reiman's upper bound
gives ex(n; C₄) ~ (1/2)n^{3/2}.

The problem is marked as SOLVED: the asymptotic formula is
  ex(n; C₄) ~ (1/2)n^{3/2}.

Erdős [Er93] also conjectured the more refined estimate
  ex(n; C₄) = n^{3/2}/2 + O(n),
which remains open (his even stronger conjecture with n/4 second-order term
was disproved by Ma–Yang [MaYa23]).
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem #765 (SOLVED):

The asymptotic formula for ex(n; C₄) is ex(n; C₄) ~ (1/2)n^{3/2}.

Formally: for every ε > 0, there exists N₀ such that for all n ≥ N₀,
  |ex(n; C₄) / n^{3/2} - 1/2| < ε.
-/
theorem erdos_problem_765 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      |(↑(extremalNumber (cycleGraph 4 (by omega)) n) / (n : ℝ) ^ ((3 : ℝ) / 2) - 1 / 2)| < ε :=
  sorry

/--
Erdős's refined conjecture from [Er93] (still open):

ex(n; C₄) = n^{3/2}/2 + O(n).

Formally: there exists a constant C > 0 such that for all n ≥ 1,
  |ex(n; C₄) - n^{3/2}/2| ≤ C · n.
-/
theorem erdos_problem_765_refined :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      |(↑(extremalNumber (cycleGraph 4 (by omega)) n) - (n : ℝ) ^ ((3 : ℝ) / 2) / 2)| ≤
        C * (n : ℝ) :=
  sorry

end
