import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #629

The list chromatic number χ_L(G) is the minimal k such that for any assignment
of a list of k colours to each vertex of G (perhaps different lists for different
vertices) a colouring of each vertex by a colour on its list can be chosen such
that adjacent vertices receive distinct colours.

Determine the minimal number of vertices n(k) of a bipartite graph G such that
χ_L(G) > k.

A problem of Erdős, Rubin, and Taylor [ERT80], who proved that
  2^{k-1} < n(k) < k² · 2^{k+2}
and n(2) = 6. Hanson, MacGillivray, and Toft [HMT96] proved n(3) = 14.
-/

/-- A proper list coloring of G with respect to a list assignment L : V → Finset ℕ
    is a function f : V → ℕ such that f(v) ∈ L(v) for all v, and f(u) ≠ f(v)
    whenever u and v are adjacent. -/
def IsProperListColoring {V : Type*} (G : SimpleGraph V) (L : V → Finset ℕ)
    (f : V → ℕ) : Prop :=
  (∀ v, f v ∈ L v) ∧ (∀ u v, G.Adj u v → f u ≠ f v)

/-- A graph G is k-choosable (k-list-colorable) if for every list assignment L
    where each vertex receives a list of at least k colors, there exists a
    proper list coloring. -/
def IsChoosable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ L : V → Finset ℕ, (∀ v, k ≤ (L v).card) →
    ∃ f : V → ℕ, IsProperListColoring G L f

/-- The list chromatic number (choice number) of a graph G: the minimum k
    such that G is k-choosable. -/
noncomputable def listChromaticNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsChoosable G k}

/-- n(k): the minimum number of vertices of a bipartite graph with list
    chromatic number greater than k. -/
noncomputable def erdos629_n (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n),
    G.Colorable 2 ∧ listChromaticNumber G > k}

/--
Erdős Problem #629, lower bound [ERT80]:
  2^{k-1} < n(k) for all k ≥ 1.
-/
theorem erdos_problem_629_lower (k : ℕ) (hk : k ≥ 1) :
    erdos629_n k > 2 ^ (k - 1) :=
  sorry

/--
Erdős Problem #629, upper bound [ERT80]:
  n(k) < k² · 2^{k+2} for all k ≥ 1.
-/
theorem erdos_problem_629_upper (k : ℕ) (hk : k ≥ 1) :
    erdos629_n k < k ^ 2 * 2 ^ (k + 2) :=
  sorry

/--
Erdős Problem #629 [ERT80]: n(2) = 6.
-/
theorem erdos_problem_629_n2 : erdos629_n 2 = 6 :=
  sorry

/--
Erdős Problem #629 [HMT96]: n(3) = 14.
-/
theorem erdos_problem_629_n3 : erdos629_n 3 = 14 :=
  sorry

end
