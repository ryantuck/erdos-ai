import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #811

Suppose n ≡ 1 (mod m). We say that an edge-colouring of K_n using m colours
is balanced if every vertex sees exactly ⌊n/m⌋ edges of each colour.

For which graphs G is it true that, if m = e(G), for all large n ≡ 1 (mod m),
every balanced edge-colouring of K_n with m colours contains a rainbow copy
of G? (That is, a subgraph isomorphic to G where each edge receives a
different colour.)

A problem of Erdős, Pyber, and Tuza [Er91][ErTu93][Er96].

A specific challenge from [Er91] and [Er96] is whether every balanced
6-colouring of K_{6k+1} contains a rainbow C₆. (The companion question about
K₄ was answered negatively by Clemen and Wagner [ClWa23].)

Axenovich and Clemen [AxCl24] proved that infinitely many complete graphs
lack this property. They conjecture K_m lacks it for all m ≥ 4.
-/

/-- The cycle graph on `m` vertices (for `m ≥ 3`): vertex `i` is adjacent
    to vertices `(i+1) mod m` and `(i-1) mod m`. -/
def cycleGraph811 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- An edge-colouring of the complete graph on `Fin n` with `m` colours is
    **balanced** if every vertex sees exactly `n / m` edges of each colour.
    (When `n ≡ 1 (mod m)`, the degree `n - 1` divides evenly as
    `m · (n / m)`.) -/
def IsBalancedColoring (n m : ℕ) (c : Sym2 (Fin n) → Fin m) : Prop :=
  ∀ (v : Fin n) (i : Fin m),
    (Finset.univ.filter (fun w : Fin n => w ≠ v ∧
      c (Sym2.mk (v, w)) = i)).card = n / m

/-- A **rainbow copy** of a graph `G` in a coloured complete graph on `Fin n`
    is an injective vertex map such that all edges of `G` receive pairwise
    distinct colours. -/
def HasRainbowCopy {V : Type*} (G : SimpleGraph V)
    {n m : ℕ} (c : Sym2 (Fin n) → Fin m) : Prop :=
  ∃ f : V → Fin n, Function.Injective f ∧
    ∀ a b a' b' : V, G.Adj a b → G.Adj a' b' →
      Sym2.mk (a, b) ≠ Sym2.mk (a', b') →
      c (Sym2.mk (f a, f b)) ≠ c (Sym2.mk (f a', f b'))

/--
**Erdős Problem #811** (specific challenge from [Er91] and [Er96]):

For all sufficiently large `n ≡ 1 (mod 6)`, every balanced edge-colouring
of `K_n` with `6` colours contains a rainbow copy of `C₆`.

The companion question about `K₄` (which also has `6` edges) was answered
negatively by Clemen and Wagner [ClWa23].
-/
theorem erdos_problem_811_conjecture :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → n % 6 = 1 →
      ∀ c : Sym2 (Fin n) → Fin 6,
        IsBalancedColoring n 6 c →
        HasRainbowCopy (cycleGraph811 6 (by omega)) c :=
  sorry

end
