-- [AI - Claude Fable 5.2]: Erdős Problem 207 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.ExistsUnique

/-!
# Erdős Problem #207

*Source:* [erdosproblems.com/207](https://www.erdosproblems.com/207) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20). [Er76]

For any $g\geq 2$, if $n$ is sufficiently large and $\equiv 1,3\pmod{6}$ then there exists a
3-uniform hypergraph on $n$ vertices such that

* every pair of vertices is contained in exactly one edge (i.e. the graph is a Steiner triple
  system) and
* for any $2\leq j\leq g$ any collection of $j$ edges contains at least $j+3$ vertices.

Remark recorded on the page: proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].

## Status

PROVED at capture and in the metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12; no
Lean proof recorded). Upstream `formal-conjectures` (`5258ab9`) states the same theorem with a
block-design predicate in place of `IsSteinerTripleSystem`.

## Encoding notes

* The theorem is a direct assertion of the proved statement. "Any collection of `j` edges" is a
  set `S ⊆ edges` with `S.card = j`, and its vertex set is `S.biUnion id`.
* In a Steiner triple system two distinct edges share at most one vertex
  (`IsSteinerTripleSystem.inter_card_le_one`, PROVED in Lean). Hence two edges span at least
  `5 = 2 + 3` vertices and three edges at least `6 = 3 + 3` (`two_edges_span`, `three_edges_span`,
  PROVED in Lean): the conditions `j = 2` and `j = 3` hold in every Steiner triple system. The
  first real restriction is `j = 4`, which excludes the Pasch configuration (four edges on six
  vertices); the Fano plane contains one (computed, not proved in Lean).
* Consequently for `g ≤ 3` the theorem is exactly the existence of Steiner triple systems for
  `n ≡ 1, 3 (mod 6)` (Kirkman): `variants.of_kirkman` (PROVED in Lean) derives the cases `g = 2`
  and `g = 3` from `variants.kirkman` (SOLVED; not proved here).
* The conclusion holds for `n = 1` and `n = 3` for every `g` (`variants.n_eq_one`,
  `variants.n_eq_three`, PROVED in Lean): there are too few edges for the condition to bite.

## References

From the site's `/latex/207` bibliography:
* [KSSS22b] Kwan, M., Sah, A., Sawhney, M. and Simkin, M., _High-girth Steiner triple systems_.
  arXiv:2201.04554 (2022).

Not in `/latex/207`:
* [Er76] Erdős, P. (**DEFERRED:** cited in the page heading; no site bibliography entry was
  recovered. Upstream's Problem 780 file gives, for the key [Er76], _Problems and results in
  combinatorial analysis_. Colloquio Internazionale sulle Teorie Combinatorie (Roma, 1973), Tomo
  II (1976), 3–17; whether that is the paper meant here was not checked.)

*Provenance:* second pass of `conjectures/207.lean` (Fable 5.2 review,
`fable-5-2-review/207.md`).
-/

/-- A set of hyperedges forms a Steiner triple system: each edge has exactly 3
    vertices, and every pair of distinct vertices appears in exactly one edge. -/
def IsSteinerTripleSystem {n : ℕ} (edges : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ edges, e.card = 3) ∧
  (∀ u v : Fin n, u ≠ v → ∃! e, e ∈ edges ∧ u ∈ e ∧ v ∈ e)

/--
Erdős Problem #207 (Proved) [Er76]:

For any g ≥ 2, if n is sufficiently large and n ≡ 1 or 3 (mod 6), there exists
a Steiner triple system on n vertices such that any j edges (for 2 ≤ j ≤ g)
span at least j + 3 vertices.

The girth condition forbids short "cycles" in the hypergraph: any collection of
j edges (for 2 ≤ j ≤ g) must contain at least j + 3 distinct vertices.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b]. Not proved here.
-/
theorem erdos_problem_207 :
    ∀ g : ℕ, 2 ≤ g →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (n % 6 = 1 ∨ n % 6 = 3) →
          ∃ edges : Finset (Finset (Fin n)),
            IsSteinerTripleSystem edges ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ g →
              ∀ S : Finset (Finset (Fin n)), S ⊆ edges → S.card = j →
                j + 3 ≤ (S.biUnion id).card :=
  sorry

/-- In a Steiner triple system two distinct edges share at most one vertex (PROVED in Lean). -/
theorem IsSteinerTripleSystem.inter_card_le_one {n : ℕ} {edges : Finset (Finset (Fin n))}
    (h : IsSteinerTripleSystem edges) {e f : Finset (Fin n)} (he : e ∈ edges) (hf : f ∈ edges)
    (hef : e ≠ f) : (e ∩ f).card ≤ 1 := by
  by_contra hcon
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (not_le.1 hcon)
  rw [Finset.mem_inter] at hu hv
  exact hef ((h.2 u v huv).unique ⟨he, hu.1, hv.1⟩ ⟨hf, hu.2, hv.2⟩)

/-- Two distinct edges of a Steiner triple system span at least `5` vertices (PROVED in Lean). -/
theorem IsSteinerTripleSystem.five_le_card_union {n : ℕ} {edges : Finset (Finset (Fin n))}
    (h : IsSteinerTripleSystem edges) {e f : Finset (Fin n)} (he : e ∈ edges) (hf : f ∈ edges)
    (hef : e ≠ f) : 5 ≤ (e ∪ f).card := by
  have h1 := Finset.card_union_add_card_inter e f
  have h2 := h.inter_card_le_one he hf hef
  have h3 := h.1 e he
  have h4 := h.1 f hf
  omega

/-- The condition `j = 2` holds in every Steiner triple system (PROVED in Lean). -/
theorem erdos_problem_207.two_edges_span {n : ℕ} {edges : Finset (Finset (Fin n))}
    (h : IsSteinerTripleSystem edges) (S : Finset (Finset (Fin n))) (hS : S ⊆ edges)
    (hcard : S.card = 2) : 2 + 3 ≤ (S.biUnion id).card := by
  obtain ⟨e, f, hef, rfl⟩ := Finset.card_eq_two.1 hcard
  have he : e ∈ edges := hS (by simp)
  have hf : f ∈ edges := hS (by simp)
  have h5 := h.five_le_card_union he hf hef
  have hU : (({e, f} : Finset (Finset (Fin n))).biUnion id) = e ∪ f := by
    ext x
    simp
  rw [hU]
  exact h5

/-- The condition `j = 3` holds in every Steiner triple system (PROVED in Lean): three edges
pairwise share at most one vertex, so they span at least `9 - 3 = 6` vertices. -/
theorem erdos_problem_207.three_edges_span {n : ℕ} {edges : Finset (Finset (Fin n))}
    (h : IsSteinerTripleSystem edges) (S : Finset (Finset (Fin n))) (hS : S ⊆ edges)
    (hcard : S.card = 3) : 3 + 3 ≤ (S.biUnion id).card := by
  obtain ⟨e, f, g, hef, heg, hfg, rfl⟩ := Finset.card_eq_three.1 hcard
  have he : e ∈ edges := hS (by simp)
  have hf : f ∈ edges := hS (by simp)
  have hg : g ∈ edges := hS (by simp)
  have hU : (({e, f, g} : Finset (Finset (Fin n))).biUnion id) = (e ∪ f) ∪ g := by
    ext x
    simp
  rw [hU]
  have h5 := h.five_le_card_union he hf hef
  have h1 := Finset.card_union_add_card_inter (e ∪ f) g
  have h2 : ((e ∪ f) ∩ g).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have h3 := Finset.card_union_le (e ∩ g) (f ∩ g)
    have h4 := h.inter_card_le_one he hg heg
    have h6 := h.inter_card_le_one hf hg hfg
    omega
  have h7 := h.1 g hg
  omega

/-- Kirkman's theorem (SOLVED, 1847; not proved here): a Steiner triple system on `n` vertices
exists whenever `n ≡ 1, 3 (mod 6)`. -/
theorem erdos_problem_207.variants.kirkman :
    ∀ n : ℕ, (n % 6 = 1 ∨ n % 6 = 3) →
      ∃ edges : Finset (Finset (Fin n)), IsSteinerTripleSystem edges :=
  sorry

/-- For `g ≤ 3` the theorem is Kirkman's theorem (PROVED in Lean, from the existence statement as
a hypothesis): the conditions `j = 2` and `j = 3` hold in every Steiner triple system, with
`N₀ = 0`. -/
theorem erdos_problem_207.variants.of_kirkman
    (hK : ∀ n : ℕ, (n % 6 = 1 ∨ n % 6 = 3) →
      ∃ edges : Finset (Finset (Fin n)), IsSteinerTripleSystem edges) :
    ∀ g : ℕ, 2 ≤ g → g ≤ 3 →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (n % 6 = 1 ∨ n % 6 = 3) →
          ∃ edges : Finset (Finset (Fin n)),
            IsSteinerTripleSystem edges ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ g →
              ∀ S : Finset (Finset (Fin n)), S ⊆ edges → S.card = j →
                j + 3 ≤ (S.biUnion id).card := by
  intro g _ hg3
  refine ⟨0, fun n _ hn => ?_⟩
  obtain ⟨edges, hE⟩ := hK n hn
  refine ⟨edges, hE, fun j hj2 hjg S hS hcard => ?_⟩
  have hj : j = 2 ∨ j = 3 := by omega
  rcases hj with rfl | rfl
  · exact erdos_problem_207.two_edges_span hE S hS hcard
  · exact erdos_problem_207.three_edges_span hE S hS hcard

/-- The conclusion holds for `n = 1` and every `g` (PROVED in Lean): no edges. -/
theorem erdos_problem_207.variants.n_eq_one (g : ℕ) :
    ∃ edges : Finset (Finset (Fin 1)),
      IsSteinerTripleSystem edges ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ g →
        ∀ S : Finset (Finset (Fin 1)), S ⊆ edges → S.card = j →
          j + 3 ≤ (S.biUnion id).card := by
  refine ⟨∅, ⟨by simp, fun u v huv => absurd (Subsingleton.elim u v) huv⟩, ?_⟩
  intro j hj2 _ S hS hcard
  have h1 := Finset.card_le_card hS
  rw [Finset.card_empty] at h1
  omega

/-- The conclusion holds for `n = 3` and every `g` (PROVED in Lean): the single edge `{0, 1, 2}`
is a Steiner triple system, and there are no two edges. -/
theorem erdos_problem_207.variants.n_eq_three (g : ℕ) :
    ∃ edges : Finset (Finset (Fin 3)),
      IsSteinerTripleSystem edges ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ g →
        ∀ S : Finset (Finset (Fin 3)), S ⊆ edges → S.card = j →
          j + 3 ≤ (S.biUnion id).card := by
  refine ⟨{Finset.univ}, ⟨?_, fun u v _ => ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_singleton] at he
    rw [he]
    rfl
  · exact ⟨Finset.univ, by simp, fun y hy => Finset.mem_singleton.1 hy.1⟩
  · intro j hj2 _ S hS hcard
    have h1 := Finset.card_le_card hS
    rw [Finset.card_singleton] at h1
    omega
