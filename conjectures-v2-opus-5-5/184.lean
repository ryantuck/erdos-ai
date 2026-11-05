-- [AI - Claude Opus 5.5]: Erdős Problem 184 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #184

*Source:* [erdosproblems.com/184](https://www.erdosproblems.com/184) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20). [EGP66]
[Er71] [Er76] [Er81] [Er83b]

Any graph on $n$ vertices can be decomposed into $O(n)$ many edge-disjoint cycles and edges.

Remarks recorded on the page (abridged): conjectured by Erdős and Gallai, who proved that
$O(n\log n)$ many cycles and edges suffices. The graph $K_{3,n-3}$ shows that at least $(1+c)n$
many cycles and edges are required, for some constant $c>0$. In [Er71] Erdős suggests that only
$n-1$ many cycles and edges are required if we do not require them to be edge-disjoint. The best
bound available is due to Bucić and Montgomery [BM22], who prove that $O(n\log^*n)$ many cycles
and edges suffice. Conlon, Fox, and Sudakov [CFS14] proved that $O_\epsilon(n)$ cycles and edges
suffice if $G$ has minimum degree at least $\epsilon n$, for any $\epsilon>0$. See also [583] for
paths and [1017] for complete graphs.

## Status after capture

Upstream `formal-conjectures` (`2befc3a`) records the problem as **solved** in the affirmative,
by an OpenAI model in September 2026 ([OAI26a]), with a linked Lean proof. The metadata mirror
(`c443d8c`) still lists it as open. Neither the preprint nor the Lean proof was read in this
review; the statement below is the direction upstream records as proved.

## Encoding notes

* A decomposition is a family `parts : Fin k → Finset (Sym2 (Fin n))` of pairwise disjoint sets
  whose union is the edge set, each a single edge or the edge set of a cycle of `G`. The `↔` makes
  every listed edge an edge of `G`, and every part is nonempty, so `k` counts real pieces.
  `IsCycleEdgeDecomposition184` bundles these three conditions for the variants; the main theorem
  is literally the bound plus this predicate (`main_iff`, PROVED in Lean).
* The conditions are satisfiable for every graph: the edges themselves form a decomposition into
  $|E|\le\binom n2$ pieces (`trivial_decomposition`, PROVED in Lean). So the content of the
  theorem is the linear bound.

## References

From the site's `/latex/184` bibliography:
* [BM22] Bucić, M. and Montgomery, R., _Towards the Erdős–Gallai Cycle Decomposition Conjecture_.
  arXiv:2211.07689 (2022).
* [CFS14] Conlon, David, Fox, Jacob and Sudakov, Benny, _Cycle packing_. Random Structures
  Algorithms (2014), 608–626.
* [Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
  Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.

Other sources:
* [EGP66] Erdős, Paul, Goodman, A. W. and Pósa, Lajos, _The representation of a graph by set
  intersections_. Canadian J. Math. (1966), 106–112. (Site `/latex/1017`.)
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42. (Site `/latex/111`.)
* [Er76], [Er83b] Erdős, P. **DEFERRED:** cited in the page heading; no site bibliography entry
  was recovered.
* [OAI26a] OpenAI, _A linear cycle-and-edge decomposition of every graph_. OpenAI Math Release
  preprint (2026). (From upstream's Problem 184 file; not read.)

*Provenance:* second pass of `conjectures/184.lean` (Opus 5.5 review, `opus-5-5-review/184.md`).
-/

/--
Erdős Problem #184 (Erdős-Gallai conjecture) [EGP66, Er71, Er76, Er81, Er83b]:

There exists a constant C > 0 such that for every n and every simple graph G on
n vertices, the edge set of G can be partitioned into at most C · n parts, where
each part is either a single edge or the edge set of a cycle in G.

(Status: OPEN at capture; upstream records it as solved by [OAI26a], unverified here.)
-/
theorem erdos_problem_184 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        (k : ℝ) ≤ C * (n : ℝ) ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k,
          (∃ e, parts i = {e}) ∨
          (∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.edges.toFinset = parts i)) :=
  sorry

/-- `parts` is a decomposition of the edge set of `G` into edge-disjoint single edges and cycles of
`G`: the three conditions of the main theorem. -/
def IsCycleEdgeDecomposition184 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {k : ℕ}
    (parts : Fin k → Finset (Sym2 (Fin n))) : Prop :=
  (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
  (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
  (∀ i : Fin k,
    (∃ e, parts i = {e}) ∨
    (∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.edges.toFinset = parts i))

/-- The main theorem is the linear bound together with `IsCycleEdgeDecomposition184` (PROVED in
Lean, by unfolding). -/
theorem erdos_problem_184.main_iff :
    (∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
          (k : ℝ) ≤ C * (n : ℝ) ∧
          (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
          (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
          (∀ i : Fin k,
            (∃ e, parts i = {e}) ∨
            (∃ (u : Fin n) (w : G.Walk u u), w.IsCycle ∧ w.edges.toFinset = parts i))) ↔
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_dG : DecidableRel G.Adj),
        ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
          (k : ℝ) ≤ C * (n : ℝ) ∧ IsCycleEdgeDecomposition184 G parts :=
  Iff.rfl

/-- Every graph decomposes into its single edges, so the conditions are satisfiable, with
$k=|E|\le\binom n2$ (PROVED in Lean). -/
theorem erdos_problem_184.trivial_decomposition {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
      k ≤ n.choose 2 ∧ IsCycleEdgeDecomposition184 G parts := by
  refine ⟨G.edgeFinset.card, fun i => {(G.edgeFinset.equivFin.symm i : Sym2 (Fin n))},
    ?_, ?_, ?_, ?_⟩
  · simpa using G.card_edgeFinset_le_card_choose_two
  · intro i j hij
    rw [Finset.disjoint_singleton]
    intro h
    exact hij (G.edgeFinset.equivFin.symm.injective (Subtype.ext h))
  · intro e
    constructor
    · intro he
      refine ⟨G.edgeFinset.equivFin ⟨e, he⟩, ?_⟩
      simp
    · rintro ⟨i, hi⟩
      rw [Finset.mem_singleton] at hi
      rw [hi]
      exact (G.edgeFinset.equivFin.symm i).2
  · intro i
    exact Or.inl ⟨_, rfl⟩

/-- Erdős and Gallai [EGP66] (SOLVED; not proved here): $O(n\log n)$ cycles and edges suffice. -/
theorem erdos_problem_184.variants.erdos_gallai :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
          (k : ℝ) ≤ C * (n : ℝ) * Real.log (n : ℝ) ∧ IsCycleEdgeDecomposition184 G parts :=
  sorry

/-- Conlon, Fox and Sudakov [CFS14] (SOLVED; not proved here): $O_\varepsilon(n)$ cycles and edges
suffice when the minimum degree is at least $\varepsilon n$. -/
theorem erdos_problem_184.variants.conlon_fox_sudakov :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        (∀ v, ε * (n : ℝ) ≤ (G.degree v : ℝ)) →
        ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
          (k : ℝ) ≤ C * (n : ℝ) ∧ IsCycleEdgeDecomposition184 G parts :=
  sorry

/-- The complete bipartite graph $K_{3,n-3}$ on `Fin n`: the vertices `0, 1, 2` on one side. -/
def k3Graph184 (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := ((i : ℕ) < 3 ∧ 3 ≤ (j : ℕ)) ∨ ((j : ℕ) < 3 ∧ 3 ≤ (i : ℕ))
  symm _ _ h := Or.symm h
  loopless := ⟨fun i h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/-- Adjacency in `k3Graph184 n` is decidable. -/
instance (n : ℕ) : DecidableRel (k3Graph184 n).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

/-- The page's lower bound (SOLVED; not proved here): $K_{3,n-3}$ needs at least $(1+c)n$ cycles and
edges, for some $c>0$ and all large $n$. -/
theorem erdos_problem_184.variants.k3_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in Filter.atTop, ∀ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
      IsCycleEdgeDecomposition184 (k3Graph184 n) parts → (1 + c) * (n : ℝ) ≤ k :=
  sorry

end
