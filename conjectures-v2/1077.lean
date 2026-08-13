import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Prod

open SimpleGraph Finset Real

noncomputable section

open Classical in
/--
The degree of vertex `v` in the subgraph of `G` induced by vertex set `S`:
the number of vertices in `S` adjacent to `v` in `G`.
-/
def inducedDegree {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : ℕ :=
  (S.filter (G.Adj v)).card

open Classical in
/--
The number of edges in the subgraph of `G` induced by `S`, computed as
half the number of ordered adjacent pairs in `S × S`.
-/
def inducedEdgeCount {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card / 2

/--
The subgraph of `G` spanned by `S` is `D`-balanced if for every pair of vertices
in `S`, the induced degree of one is at most `D` times the induced degree of the
other. Equivalently, the maximum degree is at most `D` times the minimum degree.

Note: a vertex of `S` isolated in `G` forces every vertex of `S` to be isolated,
so a `D`-balanced subgraph with at least one edge has minimum degree ≥ 1.
-/
def isDBalanced {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (D : ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, inducedDegree G S u ≤ D * inducedDegree G S v

/--
Erdős Problem #1077 [ErSi70,p.388] (DISPROVED):

We call a graph D-balanced (or D-almost-regular) if the maximum degree is at
most D times the minimum degree.

Question (Erdős–Simonovits): Let ε, α > 0 and D and n be sufficiently large.
If G is a graph on n vertices with at least n^{1+α} edges, then must G contain
a D-balanced subgraph on m > n^{1-α} vertices with at least ε·m^{1+α} edges?

This has been solved in the negative, so the theorem asserts the NEGATION of
the quoted statement. The refutation (for any fixed ε and any α < 1/2) is
witnessed by a complete bipartite graph with one side of ≈ n^α vertices: any
D-balanced subgraph with ≥ ε·m^{1+α} > 0 edges has its two sides of sizes
within a factor D of each other, hence m ≪_D n^α < n^{1-α}.

A subgraph here is a general (not necessarily induced/spanning) subgraph,
encoded as a graph H on the same vertex type whose edges lie inside G and
inside the vertex set S; m = |S|, degrees and edges are those of H within S.

Remarks from the source page (edition 08 January 2026, accessed 2026-03-09):
Erdős and Simonovits [ErSi70] proved that for any α > 0, if D and n are
sufficiently large, then any graph on n vertices with at least n^{1+α} edges
contains a D-balanced subgraph on m ≥ n^{α(1-α)/(1+α)} vertices with ≫ m^{1+α}
edges. The problem as stated reflects [ErSi70] but "does not really make
sense" as printed (ε > 0 suggests a small constant yet arbitrarily large ε is
allowed; the exponent 1-α strangely decreases in α) — possibly a typographical
error for the exponent α. JunGao showed the correct vertex-count threshold is
≍ n^α, and Jiang–Longbrake [JiLo25] proved the matching lower bound: there
always exists a 6-balanced subgraph on m ≫ n^α vertices with ≫_α m^{1+α}
edges. See also Erdős Problem #803.

References:
[ErSi70] Erdős, P. and Simonovits, M., _Some extremal problems in graph
theory_. Combinatorial theory and its applications, I–III (Proc. Colloq.,
Balatonfüred, 1969) (1970), 377–390.
[JiLo25] Jiang and Longbrake (2025). (Full bibliographic details not
recoverable offline.)
-/
theorem erdos_problem_1077 :
    ¬ (∀ ε : ℝ, 0 < ε →
       ∀ α : ℝ, 0 < α →
         ∃ D₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
           ∀ G : SimpleGraph (Fin n),
             (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) →
             ∃ (H : SimpleGraph (Fin n)) (S : Finset (Fin n)),
               (∀ u v : Fin n, H.Adj u v → G.Adj u v) ∧
               (∀ u v : Fin n, H.Adj u v → u ∈ S ∧ v ∈ S) ∧
               isDBalanced H S D ∧
               (S.card : ℝ) > (n : ℝ) ^ (1 - α) ∧
               (inducedEdgeCount H S : ℝ) ≥ ε * (S.card : ℝ) ^ (1 + α)) :=
  sorry

/--
Variant (proved) [ErSi70]: for any α > 0 there is a constant c > 0 such that,
if D and n are sufficiently large, any graph on n vertices with at least
n^{1+α} edges contains a D-balanced subgraph on m ≥ n^{α(1-α)/(1+α)} vertices
with at least c·m^{1+α} edges. (The implicit constant in the source's
"≫ m^{1+α}" is read as depending on α only.)
-/
theorem erdos_problem_1077.variants.erdos_simonovits :
    ∀ α : ℝ, 0 < α →
      ∃ c : ℝ, 0 < c ∧
        ∃ D₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          ∀ G : SimpleGraph (Fin n),
            (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) →
            ∃ (H : SimpleGraph (Fin n)) (S : Finset (Fin n)),
              (∀ u v : Fin n, H.Adj u v → G.Adj u v) ∧
              (∀ u v : Fin n, H.Adj u v → u ∈ S ∧ v ∈ S) ∧
              isDBalanced H S D ∧
              (S.card : ℝ) ≥ (n : ℝ) ^ (α * (1 - α) / (1 + α)) ∧
              (inducedEdgeCount H S : ℝ) ≥ c * (S.card : ℝ) ^ (1 + α) :=
  sorry

/--
Variant (proved) [JiLo25]: for any α > 0 there are constants c₁, c₂ > 0 such
that, for all sufficiently large n, any graph on n vertices with at least
n^{1+α} edges contains a 6-balanced subgraph on m ≥ c₁·n^α vertices with at
least c₂·m^{1+α} edges. This is the lower bound matching JunGao's upper bound,
showing the correct vertex-count threshold in Problem #1077 is ≍ n^α.
-/
theorem erdos_problem_1077.variants.jiang_longbrake :
    ∀ α : ℝ, 0 < α →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          ∀ G : SimpleGraph (Fin n),
            (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) →
            ∃ (H : SimpleGraph (Fin n)) (S : Finset (Fin n)),
              (∀ u v : Fin n, H.Adj u v → G.Adj u v) ∧
              (∀ u v : Fin n, H.Adj u v → u ∈ S ∧ v ∈ S) ∧
              isDBalanced H S 6 ∧
              (S.card : ℝ) ≥ c₁ * (n : ℝ) ^ α ∧
              (inducedEdgeCount H S : ℝ) ≥ c₂ * (S.card : ℝ) ^ (1 + α) :=
  sorry

/--
Variant (proved; upper bound, shown by JunGao, witnessed by a complete
bipartite graph with one side of ≈ n^α vertices): for any 0 < α < 1, ε > 0 and
any D, there is C > 0 such that for all sufficiently large n some graph on n
vertices with at least n^{1+α} edges has every D-balanced subgraph with at
least ε·m^{1+α} edges on m ≤ C·n^α vertices. Hence no more than ≪ n^α
vertices is possible in general in Problem #1077.
-/
theorem erdos_problem_1077.variants.vertex_upper_bound :
    ∀ α : ℝ, 0 < α → α < 1 →
      ∀ ε : ℝ, 0 < ε →
        ∀ D : ℕ, ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
            ∃ G : SimpleGraph (Fin n),
              (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) ∧
              ∀ (H : SimpleGraph (Fin n)) (S : Finset (Fin n)),
                (∀ u v : Fin n, H.Adj u v → G.Adj u v) →
                (∀ u v : Fin n, H.Adj u v → u ∈ S ∧ v ∈ S) →
                isDBalanced H S D →
                (inducedEdgeCount H S : ℝ) ≥ ε * (S.card : ℝ) ^ (1 + α) →
                (S.card : ℝ) ≤ C * (n : ℝ) ^ α :=
  sorry

/--
Variant (proved): the source page's suggested repair of the original problem
statement — "let α > 0 and D and n be sufficiently large; there exists
ε = ε(α) > 0 such that if G is a graph on n vertices with at least n^{1+α}
edges then G must contain a D-balanced subgraph on m > ε·n^α vertices with at
least ε·m^{1+α} edges". This corrected form holds by [JiLo25] (a 6-balanced
subgraph is D-balanced for every D ≥ 6).
-/
theorem erdos_problem_1077.variants.corrected_statement :
    ∀ α : ℝ, 0 < α →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ D₀ : ℕ, ∀ D : ℕ, D ≥ D₀ → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
          ∀ G : SimpleGraph (Fin n),
            (inducedEdgeCount G Finset.univ : ℝ) ≥ (n : ℝ) ^ (1 + α) →
            ∃ (H : SimpleGraph (Fin n)) (S : Finset (Fin n)),
              (∀ u v : Fin n, H.Adj u v → G.Adj u v) ∧
              (∀ u v : Fin n, H.Adj u v → u ∈ S ∧ v ∈ S) ∧
              isDBalanced H S D ∧
              (S.card : ℝ) > ε * (n : ℝ) ^ α ∧
              (inducedEdgeCount H S : ℝ) ≥ ε * (S.card : ℝ) ^ (1 + α) :=
  sorry

end
