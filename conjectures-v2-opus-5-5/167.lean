-- [AI - Claude Opus 5.5]: Erdős Problem 167 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Finset.Sym
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #167 (Tuza's conjecture)

*Source:* [erdosproblems.com/167](https://www.erdosproblems.com/167) (status **FALSIFIABLE**: "Open,
but could be disproved with a finite counterexample."; captured 2026-02-20; page edited 13 October
2025). [Er88]

If $G$ is a graph with at most $k$ edge disjoint triangles then can $G$ be made triangle-free after
removing at most $2k$ edges?

Remarks recorded on the page: a problem of Tuza. It is trivial that $G$ can be made triangle-free
after removing at most $3k$ edges. The examples of $K_4$ and $K_5$ show that $2k$ would be best
possible. The trivial bound of $\le3k$ was improved to $\le(3-\frac3{23}+o(1))k$ by Haxell [Ha99].
Kahn and Park [KaPa22] have proved this is true for random graphs.

## Encoding notes

* The question is a yes/no question with open status; the "yes" direction (Tuza's conjecture,
  $\tau(G)\le2\nu(G)$) is asserted, for every finite simple graph.
* "At most $k$ edge-disjoint triangles" is `hpack`: every family of `3`-cliques that pairwise share
  at most one vertex has at most `k` members. Two distinct triangles share an edge exactly when they
  share two vertices, so this is $\nu(G)\le k$.
* "Made triangle-free after removing at most $2k$ edges" is a triangle-free `H ≤ G` with at most
  `2k` edges of `G` missing from `H` (`ncard` of a finite set, since `V` is finite).
* Checks on the encoding (PROVED in Lean): the trivial bound $\tau\le3k$ follows from `hpack`
  (`variants.three_k`, by deleting the edges of a maximum packing), and $K_4$ has
  $\nu(K_4)\le1$ but needs two deletions (`variants.k4_pack`, `variants.k4_cover`), so `2 * k`
  cannot be replaced by `2 * k - 1` (`variants.two_k_best`).
* Kahn and Park's theorem concerns random graphs and is not formalized here.

## References

* [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_. Discrete
  Math. (1988), 81–92. (Site `/latex/77`, `/latex/151`, `/latex/934`.)
* [Ha99] Haxell, P. E., _Packing and covering triangles in graphs_. Discrete Math. 195 (1999),
  251–254. (**DEFERRED:** from the archived DeepMind copy; no site entry was recovered.)
* [KaPa22] Kahn, J. and Park, J., _Tuza's conjecture for random graphs_. Random Structures &
  Algorithms 61 (2022), 235–249. (**DEFERRED:** from the archived DeepMind copy; no site entry was
  recovered.)

*Provenance:* second pass of `conjectures/167.lean` (Opus 5.5 review, `opus-5-5-review/167.md`).
-/

open SimpleGraph Finset

noncomputable section

/--
Erdős Conjecture (Problem #167) — Tuza's Conjecture [Er88]:

For any finite simple graph G, if the maximum number of pairwise edge-disjoint
triangles in G is at most k, then G can be made triangle-free by removing at
most 2k edges.

Two triangles (3-cliques) are edge-disjoint iff their vertex sets share at most
one vertex, since in a triangle every pair of vertices forms an edge.

The hypothesis states that every family of pairwise edge-disjoint triangles
has size at most k. The conclusion states that there exists a subgraph H ≤ G
that is triangle-free, obtained by removing at most 2k edges from G.
(Status: FALSIFIABLE, open.)
-/
theorem erdos_problem_167
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    -- Hypothesis: every family of pairwise edge-disjoint triangles has size ≤ k
    (hpack : ∀ (T : Finset (Finset V)),
      (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
      T.card ≤ k) :
    -- Conclusion: G can be made triangle-free by removing ≤ 2k edges
    ∃ (H : SimpleGraph V),
      H ≤ G ∧
      H.CliqueFree 3 ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ 2 * k :=
  sorry

/-- The trivial bound (PROVED in Lean): under the same hypothesis `hpack`, `G` can be made
triangle-free by removing at most `3k` edges. Take a packing `T` of maximum size; deleting the at
most `3|T| ≤ 3k` edges of its triangles leaves no triangle, since a remaining triangle would share
at most one vertex with each member of `T` and so could be added to it. -/
theorem erdos_problem_167.variants.three_k
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    (hpack : ∀ (T : Finset (Finset V)),
      (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
      T.card ≤ k) :
    ∃ (H : SimpleGraph V),
      H ≤ G ∧
      H.CliqueFree 3 ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ 3 * k := by
  classical
  let P : Finset (Finset V) → Prop := fun T =>
    (∀ t ∈ T, G.IsNClique 3 t) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1)
  obtain ⟨T, hTmem, hTmax⟩ := Finset.exists_max_image (Finset.univ.filter P) Finset.card
    ⟨∅, by simp [P]⟩
  rw [Finset.mem_filter] at hTmem
  obtain ⟨-, hTcl, hTdisj⟩ := hTmem
  let D : Finset (Sym2 V) := T.biUnion (fun t => t.sym2 ∩ G.edgeFinset)
  refine ⟨G.deleteEdges (D : Set (Sym2 V)), G.deleteEdges_le _, ?_, ?_⟩
  · intro s hs
    have hsG : G.IsNClique 3 s := hs.mono (G.deleteEdges_le _)
    have key : ∀ t ∈ T, (s ∩ t).card ≤ 1 := by
      intro t ht
      by_contra hlt
      push_neg at hlt
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
      rw [Finset.mem_inter] at hx hy
      have hadj : (G.deleteEdges (D : Set (Sym2 V))).Adj x y := hs.1 hx.1 hy.1 hxy
      rw [SimpleGraph.deleteEdges_adj] at hadj
      apply hadj.2
      simp only [D, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_inter,
        Finset.mem_sym2_iff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨t, ht, ?_, hadj.1⟩
      intro z hz
      rw [Sym2.mem_iff] at hz
      rcases hz with rfl | rfl
      · exact hx.2
      · exact hy.2
    by_cases hsT : s ∈ T
    · have := key s hsT
      rw [Finset.inter_self, hsG.2] at this
      omega
    · have hP : P (insert s T) := by
        refine ⟨?_, ?_⟩
        · intro t ht
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hsG
          · exact hTcl t ht
        · intro t₁ ht₁ t₂ ht₂ hne
          rcases Finset.mem_insert.mp ht₁ with h₁ | h₁ <;>
            rcases Finset.mem_insert.mp ht₂ with h₂ | h₂
          · exact absurd (h₁.trans h₂.symm) hne
          · rw [h₁]; exact key t₂ h₂
          · rw [h₂, Finset.inter_comm]; exact key t₁ h₁
          · exact hTdisj t₁ h₁ t₂ h₂ hne
      have := hTmax (insert s T) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)
      rw [Finset.card_insert_of_notMem hsT] at this
      omega
  · have hT : T.card ≤ k := hpack T hTcl hTdisj
    have hsub : G.edgeSet \ (G.deleteEdges (D : Set (Sym2 V))).edgeSet ⊆ (D : Set (Sym2 V)) := by
      intro e he
      rw [SimpleGraph.edgeSet_deleteEdges] at he
      by_contra hn
      exact he.2 ⟨he.1, hn⟩
    have hle : ∀ t ∈ T, (t.sym2 ∩ G.edgeFinset).card ≤ 3 := by
      intro t ht
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp (hTcl t ht).2
      calc (({a, b, c} : Finset V).sym2 ∩ G.edgeFinset).card
          ≤ ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).card := by
            apply Finset.card_le_card
            intro e he
            rw [Finset.mem_inter, Finset.mem_sym2_iff, SimpleGraph.mem_edgeFinset] at he
            induction e using Sym2.ind with
            | h x y =>
              have hx := he.1 x (Sym2.mem_mk_left x y)
              have hy := he.1 y (Sym2.mem_mk_right x y)
              have hxy : x ≠ y := G.ne_of_adj he.2
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy ⊢
              rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
                simp_all
        _ ≤ 3 := Finset.card_le_three
    have hcardD : D.card ≤ 3 * T.card := by
      calc D.card ≤ ∑ t ∈ T, (t.sym2 ∩ G.edgeFinset).card := Finset.card_biUnion_le
        _ ≤ ∑ _t ∈ T, 3 := Finset.sum_le_sum hle
        _ = 3 * T.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    calc (G.edgeSet \ (G.deleteEdges (D : Set (Sym2 V))).edgeSet).ncard
        ≤ (D : Set (Sym2 V)).ncard := Set.ncard_le_ncard hsub (D : Set (Sym2 V)).toFinite
      _ = D.card := Set.ncard_coe_finset D
      _ ≤ 3 * T.card := hcardD
      _ ≤ 3 * k := Nat.mul_le_mul_left 3 hT

/-- $K_4$ has no two edge-disjoint triangles: any two triangles in four vertices share two
vertices (PROVED in Lean). -/
theorem erdos_problem_167.variants.k4_pack :
    ∀ (T : Finset (Finset (Fin 4))),
      (∀ t ∈ T, (⊤ : SimpleGraph (Fin 4)).IsNClique 3 t) →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
      T.card ≤ 1 := by
  intro T hcl hdisj
  rw [Finset.card_le_one]
  intro t₁ h₁ t₂ h₂
  by_contra hne
  have hi := hdisj t₁ h₁ t₂ h₂ hne
  have hu : (t₁ ∪ t₂).card ≤ 4 := by
    calc (t₁ ∪ t₂).card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_le_univ _
      _ = 4 := by simp
  have := Finset.card_union_add_card_inter t₁ t₂
  rw [(hcl t₁ h₁).2, (hcl t₂ h₂).2] at this
  omega

/-- $K_4$ cannot be made triangle-free by removing one edge (PROVED in Lean): the triangles
`{0,1,2}`, `{0,1,3}`, `{0,2,3}` have no common edge. -/
theorem erdos_problem_167.variants.k4_cover :
    ¬ ∃ (H : SimpleGraph (Fin 4)),
      H ≤ ⊤ ∧
      H.CliqueFree 3 ∧
      ((⊤ : SimpleGraph (Fin 4)).edgeSet \ H.edgeSet).ncard ≤ 1 := by
  rintro ⟨H, -, hH, hcard⟩
  rw [Set.ncard_le_one] at hcard
  -- each of three triangles has an edge missing from H
  have miss : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
      ∃ e ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet \ H.edgeSet, e = s(a, b) ∨ e = s(a, c) ∨ e = s(b, c) := by
    intro a b c hab hac hbc
    have := hH {a, b, c}
    rw [SimpleGraph.is3Clique_triple_iff] at this
    by_cases h1 : H.Adj a b
    · by_cases h2 : H.Adj a c
      · have h3 : ¬ H.Adj b c := fun h3 => this ⟨h1, h2, h3⟩
        exact ⟨s(b, c), ⟨by simpa using hbc, h3⟩, Or.inr (Or.inr rfl)⟩
      · exact ⟨s(a, c), ⟨by simpa using hac, h2⟩, Or.inr (Or.inl rfl)⟩
    · exact ⟨s(a, b), ⟨by simpa using hab, h1⟩, Or.inl rfl⟩
  obtain ⟨e₁, he₁, h₁⟩ := miss 0 1 2 (by decide) (by decide) (by decide)
  obtain ⟨e₂, he₂, h₂⟩ := miss 0 1 3 (by decide) (by decide) (by decide)
  obtain ⟨e₃, he₃, h₃⟩ := miss 0 2 3 (by decide) (by decide) (by decide)
  have h12 := hcard e₁ he₁ e₂ he₂
  have h13 := hcard e₁ he₁ e₃ he₃
  subst h12 h13
  rcases h₁ with rfl | rfl | rfl
  · revert h₃; decide
  · revert h₂; decide
  · revert h₂; decide

/-- So the constant `2` in the main theorem cannot be lowered: with `2 * k - 1` in place of `2 * k`,
the statement fails for $K_4$ and `k = 1` (PROVED in Lean). -/
theorem erdos_problem_167.variants.two_k_best :
    ¬ ∀ k : ℕ,
      (∀ (T : Finset (Finset (Fin 4))),
        (∀ t ∈ T, (⊤ : SimpleGraph (Fin 4)).IsNClique 3 t) →
        (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
        T.card ≤ k) →
      ∃ (H : SimpleGraph (Fin 4)),
        H ≤ ⊤ ∧
        H.CliqueFree 3 ∧
        ((⊤ : SimpleGraph (Fin 4)).edgeSet \ H.edgeSet).ncard ≤ 2 * k - 1 := by
  intro h
  exact erdos_problem_167.variants.k4_cover (h 1 erdos_problem_167.variants.k4_pack)

/-- Haxell [Ha99] (SOLVED, as recorded on the page; not proved here): for every `ε > 0` and all
large `k`, a graph with at most `k` edge-disjoint triangles can be made triangle-free by removing
at most `(3 - 3/23 + ε) k` edges. -/
theorem erdos_problem_167.variants.haxell :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
    ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (k : ℕ), K ≤ k →
      (∀ (T : Finset (Finset V)),
        (∀ t ∈ T, G.IsNClique 3 t) →
        (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
        T.card ≤ k) →
      ∃ (H : SimpleGraph V),
        H ≤ G ∧
        H.CliqueFree 3 ∧
        ((G.edgeSet \ H.edgeSet).ncard : ℝ) ≤ (3 - 3 / 23 + ε) * k :=
  sorry

end
