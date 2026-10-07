-- [AI - Claude Sonnet 5.5]: Erdős Problem 149 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open SimpleGraph

/-!
# Erdős Problem #149: The strong chromatic index and the bound $\frac54\Delta^2$

*Source:* [erdosproblems.com/149](https://www.erdosproblems.com/149) (banner **OPEN**: "This is open, and
cannot be resolved with a finite computation."; page last edited 1 February 2026; captured 2026-02-20 as the page
and as the tidied problem box, with identical content). [Er88]

Let $G$ be a graph with maximum degree $\Delta$. Is $G$ the union of at most $\tfrac{5}{4}\Delta^2$ sets of
strongly independent edges (sets such that the induced subgraph is the union of vertex-disjoint edges)?

Remarks recorded on the page:
* Asked by Erdős and Nešetřil in 1985 (see [FGST89]). This is equivalent to asking whether the chromatic number
  of the square of the line graph $L(G)^2$ is at most $\frac{5}{4}\Delta^2$.
* This bound would be the best possible, as witnessed by a blowup of $C_5$. The minimum number of such sets
  required is sometimes called the strong chromatic index of $G$.
* The weaker conjecture that there exists some $c>0$ such that $(2-c)\Delta^2$ sets suffice was proved by Molloy
  and Reed [MoRe97], who proved that $1.998\Delta^2$ sets suffice (for $\Delta$ sufficiently large). This was
  improved to $1.93\Delta^2$ by Bruhn and Joos [BrJo18] and to $1.835\Delta^2$ by Bonamy, Perrett, and Postle
  [BPP22]. The best bound currently available is $1.772\Delta^2$, proved by Hurley, de Joannis de Verclos, and
  Kang [HJK22]. Mahdian has, in their Masters' thesis, proved an upper bound of
  $(2+o(1))\frac{\Delta^2}{\log \Delta}$ under the additional assumption that $G$ is $C_4$-free.
* Erdős and Nešetřil also asked the easier problem of whether $G$ containing at least $\tfrac{5}{4}\Delta^2$ many
  edges implies $G$ containing two strongly independent edges. This was proved by Chung, Gyárfás, Tuza, and
  Trotter [CGTT90].
* It is still open even whether the clique number of $L(G)^2$ is at most $\frac{5}{4}\Delta^2$. Let
  $\omega=\omega(L(G)^2)$ be this clique number. Śleszyńska-Nowak [Sl16] proved $\omega \leq \frac{3}{2}\Delta^2$.
  Faron and Postle [FaPo19] proved $\omega\leq \frac{4}{3}\Delta^2$. Cames van Batenburg, Kang, and Pirot [CKP20]
  have proved $\omega\leq \frac{5}{4}\Delta^2$ under the additional assumption that $G$ is triangle-free (and
  $\omega\leq \Delta^2$ if $G$ is $C_5$-free).

Tags: graph theory. 4 comments at capture (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31, no prize. Upstream has no
`149.lean`.

**Encoding.**
* `IsStronglyIndepEdgeSet G S` says that `S` is a set of edges of `G` in which any two distinct edges have four
  distinct endpoints and no edge of `G` joins an endpoint of one to an endpoint of the other, that is, an
  induced matching.
* `strongChromaticIndex G` is the least `k` with a colouring `c : G.edgeSet → Fin k` in which two distinct edges of
  the same colour are strongly independent. `variants.strongChromaticIndex_iff` proves that this is the same as
  "every colour class is `IsStronglyIndepEdgeSet`", which ties the first definition (not used elsewhere in the
  first pass) to the second. For a finite `G` a colouring exists (give each edge its own colour), so the set of
  admissible `k` is nonempty and `sInf` is its least element.
* `variants.strongChromaticIndex_eq_chromaticNumber` proves that `strongChromaticIndex G` is the chromatic number of
  the square of Mathlib's `SimpleGraph.lineGraph` (`erdos_problem_149.graphSq` is the square of a graph: distinct
  vertices at distance at most 2), as the page and the first pass's docstring say. `variants.chromaticNumber_form`
  states the page's equivalence for the bound.
* "Union" in the page is a cover, and a cover can be made a partition, since a subset of a strongly independent set
  is strongly independent. The bound `5/4 * Δ ^ 2` is real, and `χ'_s` is an integer, so the statement says
  `χ'_s ≤ ⌊5Δ²/4⌋`.
* `variants.strongChromaticIndex_eq_card_of_close` proves that when every two edges share a vertex or are joined by
  an edge, $\chi'_s(G)$ is the number of edges. `variants.c5_strongChromaticIndex` and `variants.c5_sharp` use it to
  prove in Lean that $\chi'_s(C_5)=5$ and $\Delta(C_5)=2$, so $C_5$ meets the bound $\frac54\Delta^2=5$ with
  equality. `variants.blowup_sharp` does the same for the blow-up of $C_5$ by $k$ independent vertices
  (`erdos_problem_149.blowupC5 k`): $\Delta=2k$ and $\chi'_s=5k^2=\frac54\Delta^2$ for every $k\ge1$, which is
  the page's sharpness ("witnessed by a blowup of $C_5$") and shows that the constant $\frac54$ cannot be lowered.
* `variants.clique_le_strongChromaticIndex` proves that every set of pairwise "close" edges has at most
  $\chi'_s(G)$ elements, so the main theorem implies the clique-number question (`variants.clique_conjecture_of_main`).
* The page's partial results are variants (`StrongBound`, `mahdian`, `sleszynska_nowak`, `faron_postle`,
  `ckp_triangle_free`, `ckp_c5_free`, `cgtt`). "$C_4$-free" and "$C_5$-free" are read as having no such subgraph
  (not necessarily induced), which gives a weaker statement than the induced reading would. **DEFERRED:** which
  reading the sources use.
* The page's wording of [CGTT90], "at least $\frac54\Delta^2$ edges", is false at $C_5$ (5 edges, $\Delta=2$, no two
  strongly independent edges): `variants.page_wording_of_cgtt_false`. The theorem says that a graph with no two
  strongly independent edges has at most $\frac54\Delta^2$ edges, which is `variants.cgtt`.

## References

* [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_. Discrete Math. (1988),
  81–92.
* [CGTT90] Chung, F. R. K., Gyárfás, A., Tuza, Z. and Trotter, W. T., _The maximum number of edges in
  $2K_2$-free graphs of bounded degree_. Discrete Math. (1990), 129–135.
* [FGST89], [MoRe97], [BrJo18], [BPP22], [HJK22], [Sl16], [FaPo19], [CKP20] cited on the page. **DEFERRED:** no
  bibliographic data was recovered for any of them.
* Mahdian's Masters' thesis (no key on the page). **DEFERRED:** no data.

(Provenance: [Er88] is from the `/latex/934`, `/latex/77` and `/latex/151` fetches in the session logs, and
[CGTT90] from the `/latex/934` fetch. **DEFERRED:** no `/latex/149` fetch exists in the logs, so the page's own
bibliography was not seen.)
-/

/-- A set S of edges of G is strongly independent if for any two distinct edges
    e₁, e₂ ∈ S, every endpoint u of e₁ and every endpoint v of e₂ satisfy
    u ≠ v and ¬G.Adj u v.  Equivalently, S is an independent set in L(G)²
    (the square of the line graph of G). -/
def IsStronglyIndepEdgeSet {V : Type*} (G : SimpleGraph V)
    (S : Set (Sym2 V)) : Prop :=
  S ⊆ G.edgeSet ∧
  ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ →
    ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬G.Adj u v

/-- The strong chromatic index χ'_s(G): the minimum number of strongly
    independent edge sets needed to partition the edges of G. Equivalently,
    this is the chromatic number of L(G)², the square of the line graph. -/
noncomputable def strongChromaticIndex {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (c : G.edgeSet → Fin k),
    ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v}

/-- Erdős–Nešetřil Strong Edge Coloring Conjecture (Erdős Problem #149) [Er88] — OPEN:
    For any finite graph G with maximum degree Δ,
      χ'_s(G) ≤ (5/4) · Δ²,
    i.e. the edge set of G can be partitioned into at most (5/4)Δ² strongly
    independent edge sets.  This bound is sharp: a blowup of C₅ with Δ = 2k
    requires exactly 5k² = (5/4)Δ² strong colors. -/
theorem erdos_problem_149 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (strongChromaticIndex G : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 :=
  sorry

/--
A colouring is a strong edge colouring iff each colour class is strongly independent (PROVED in Lean): the two
ways of writing the definition agree.
-/
theorem erdos_problem_149.variants.strongChromaticIndex_iff {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    (∃ (c : G.edgeSet → Fin k), ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v) ↔
    ∃ (c : G.edgeSet → Fin k), ∀ i : Fin k,
      IsStronglyIndepEdgeSet G {e | ∃ x : G.edgeSet, c x = i ∧ (x : Sym2 V) = e} := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => ⟨?_, ?_⟩⟩
    · rintro e ⟨x, -, rfl⟩
      exact x.2
    · rintro e₁ ⟨x₁, hx₁, rfl⟩ e₂ ⟨x₂, hx₂, rfl⟩ hne u hu v hv
      have hne' : x₁ ≠ x₂ := fun h => hne (by rw [h])
      exact hc x₁ x₂ (hx₁.trans hx₂.symm) hne' u hu v hv
  · rintro ⟨c, hc⟩
    refine ⟨c, fun e₁ e₂ h hne u hu v hv => ?_⟩
    have hne' : (e₁ : Sym2 V) ≠ (e₂ : Sym2 V) := fun h' => hne (Subtype.ext h')
    exact (hc (c e₁)).2 _ ⟨e₁, rfl, rfl⟩ _ ⟨e₂, h.symm, rfl⟩ hne' u hu v hv

/-- The square `H²` of a graph: two distinct vertices are adjacent when they are adjacent in `H` or have a common
neighbour (that is, at distance at most `2`). -/
def erdos_problem_149.graphSq {W : Type*} (H : SimpleGraph W) : SimpleGraph W where
  Adj a b := a ≠ b ∧ (H.Adj a b ∨ ∃ c, H.Adj a c ∧ H.Adj c b)
  symm := by
    rintro a b ⟨hab, h | ⟨c, h1, h2⟩⟩
    · exact ⟨hab.symm, Or.inl h.symm⟩
    · exact ⟨hab.symm, Or.inr ⟨c, h2.symm, h1.symm⟩⟩

/-- Two distinct vertices of an edge of `G` are adjacent in `G` (PROVED in Lean). -/
theorem erdos_problem_149.adj_of_mem_edge {V : Type*} {G : SimpleGraph V} (f : G.edgeSet) {a b : V}
    (ha : a ∈ (f : Sym2 V)) (hb : b ∈ (f : Sym2 V)) (hab : a ≠ b) : G.Adj a b := by
  obtain ⟨f, hf⟩ := f
  induction f using Sym2.ind with
  | _ x y =>
  rw [SimpleGraph.mem_edgeSet] at hf
  have ha' : a ∈ s(x, y) := ha
  have hb' : b ∈ s(x, y) := hb
  rw [Sym2.mem_iff] at ha' hb'
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact absurd rfl hab
  · exact hf
  · exact hf.symm
  · exact absurd rfl hab

/-- In the square of Mathlib's line graph of `G`, two edges are adjacent iff they are distinct and share a vertex or
are joined by an edge of `G` (PROVED in Lean). -/
theorem erdos_problem_149.graphSq_lineGraph_adj_iff {V : Type*} (G : SimpleGraph V) (e₁ e₂ : G.edgeSet) :
    (erdos_problem_149.graphSq G.lineGraph).Adj e₁ e₂ ↔
      e₁ ≠ e₂ ∧ ∃ u ∈ (e₁ : Sym2 V), ∃ v ∈ (e₂ : Sym2 V), u = v ∨ G.Adj u v := by
  constructor
  · rintro ⟨hne, h | ⟨f, h1, h2⟩⟩
    · obtain ⟨-, v, hv1, hv2⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp h
      exact ⟨hne, v, hv1, v, hv2, Or.inl rfl⟩
    · obtain ⟨-, a, ha1, ha2⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp h1
      obtain ⟨-, b, hb1, hb2⟩ := (SimpleGraph.lineGraph_adj_iff_exists).mp h2
      by_cases hab : a = b
      · subst hab
        exact ⟨hne, a, ha1, a, hb2, Or.inl rfl⟩
      · exact ⟨hne, a, ha1, b, hb2, Or.inr (erdos_problem_149.adj_of_mem_edge f ha2 hb1 hab)⟩
  · rintro ⟨hne, u, hu, v, hv, h | h⟩
    · refine ⟨hne, Or.inl ?_⟩
      exact (SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨hne, u, hu, h ▸ hv⟩
    · refine ⟨hne, ?_⟩
      set f : G.edgeSet := ⟨s(u, v), by simpa using h⟩ with hf
      by_cases h1 : f = e₁
      · left
        refine (SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨hne, v, ?_, hv⟩
        rw [← h1]; simp [hf]
      · by_cases h2 : f = e₂
        · left
          refine (SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨hne, u, hu, ?_⟩
          rw [← h2]; simp [hf]
        · right
          refine ⟨f, ?_, ?_⟩
          · exact (SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨fun h' => h1 h'.symm, u, hu, by simp [hf]⟩
          · exact (SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨h2, v, by simp [hf], hv⟩

/--
`χ'_s(G)` is the chromatic number of the square of the line graph (PROVED in Lean): this is the page's "equivalent to
asking whether the chromatic number of the square of the line graph `L(G)²` is at most `5/4 * Δ ^ 2`", with Mathlib's
`SimpleGraph.lineGraph` and `SimpleGraph.chromaticNumber`.
-/
theorem erdos_problem_149.variants.strongChromaticIndex_eq_chromaticNumber {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (strongChromaticIndex G : ℕ∞) = (erdos_problem_149.graphSq G.lineGraph).chromaticNumber := by
  have hset : {k : ℕ | ∃ (c : G.edgeSet → Fin k), ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v} =
      {k | (erdos_problem_149.graphSq G.lineGraph).Colorable k} := by
    ext k
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨SimpleGraph.Coloring.mk c ?_⟩
      intro e₁ e₂ hadj heq
      obtain ⟨hne, u, hu, v, hv, h⟩ := (erdos_problem_149.graphSq_lineGraph_adj_iff G e₁ e₂).mp hadj
      have := hc e₁ e₂ heq hne u hu v hv
      rcases h with h | h
      · exact this.1 h
      · exact this.2 h
    · rintro ⟨C⟩
      refine ⟨C, ?_⟩
      intro e₁ e₂ heq hne u hu v hv
      by_contra hcon
      have hadj : (erdos_problem_149.graphSq G.lineGraph).Adj e₁ e₂ := by
        rw [erdos_problem_149.graphSq_lineGraph_adj_iff]
        refine ⟨hne, u, hu, v, hv, ?_⟩
        by_cases huv : u = v
        · exact Or.inl huv
        · right
          by_contra hna
          exact hcon ⟨huv, hna⟩
      exact C.valid hadj heq
  have hc : (erdos_problem_149.graphSq G.lineGraph).Colorable (Fintype.card G.edgeSet) :=
    SimpleGraph.colorable_of_fintype _
  rw [hc.chromaticNumber_eq_sInf, ← hset]
  rfl

/--
The main theorem in the page's form (PROVED in Lean): the chromatic number of `L(G)²` is at most `5/4 * Δ ^ 2` (that
is, at most its integer part) iff `χ'_s(G) ≤ 5/4 * Δ ^ 2`.
-/
theorem erdos_problem_149.variants.chromaticNumber_form {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (erdos_problem_149.graphSq G.lineGraph).chromaticNumber ≤ ⌊(5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2⌋₊ ↔
      (strongChromaticIndex G : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 := by
  rw [← erdos_problem_149.variants.strongChromaticIndex_eq_chromaticNumber, Nat.cast_le]
  exact Nat.le_floor_iff (by positivity)

/--
If any two distinct edges of `G` share a vertex or are joined by an edge of `G`, then `χ'_s(G)` is the number of
edges (PROVED in Lean): all the colours must be different.
-/
theorem erdos_problem_149.variants.strongChromaticIndex_eq_card_of_close {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hclose : ∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ →
      ∃ u ∈ (e₁ : Sym2 V), ∃ v ∈ (e₂ : Sym2 V), u = v ∨ G.Adj u v) :
    strongChromaticIndex G = Fintype.card G.edgeSet := by
  unfold strongChromaticIndex
  have hset : {k : ℕ | ∃ (c : G.edgeSet → Fin k), ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
        ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v} =
      {k | Fintype.card G.edgeSet ≤ k} := by
    ext k
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc⟩
      have hinj : Function.Injective c := by
        intro e₁ e₂ h
        by_contra hne
        obtain ⟨u, hu, v, hv, huv⟩ := hclose e₁ e₂ hne
        have := hc e₁ e₂ h hne u hu v hv
        rcases huv with h1 | h1
        · exact this.1 h1
        · exact this.2 h1
      simpa using Fintype.card_le_of_injective c hinj
    · intro hk
      have : Nonempty (G.edgeSet ↪ Fin k) :=
        Function.Embedding.nonempty_of_card_le (by simpa using hk)
      obtain ⟨f⟩ := this
      exact ⟨f, fun e₁ e₂ h hne => absurd (f.injective h) hne⟩
  rw [hset]
  exact le_antisymm (Nat.sInf_le (Set.mem_setOf_eq ▸ le_rfl))
    (le_csInf ⟨Fintype.card G.edgeSet, (le_rfl : Fintype.card G.edgeSet ≤ Fintype.card G.edgeSet)⟩
      (fun b hb => hb))

/--
The five-cycle needs five strong colours (PROVED in Lean): any two distinct edges of `C₅` share a vertex or are
joined by an edge, so all five colours differ.
-/
theorem erdos_problem_149.variants.c5_strongChromaticIndex :
    strongChromaticIndex (cycleGraph 5) = 5 := by
  have hclose : ∀ e₁ e₂ : (cycleGraph 5).edgeSet, e₁ ≠ e₂ →
      ∃ u ∈ (e₁ : Sym2 (Fin 5)), ∃ v ∈ (e₂ : Sym2 (Fin 5)), u = v ∨ (cycleGraph 5).Adj u v := by
    decide
  have hcard : Fintype.card (cycleGraph 5).edgeSet = 5 := by decide
  rw [erdos_problem_149.variants.strongChromaticIndex_eq_card_of_close _ hclose, hcard]

/-- `C₅` has maximum degree `2` and meets the bound `5 / 4 * Δ ^ 2 = 5` with equality (PROVED in Lean). -/
theorem erdos_problem_149.variants.c5_sharp :
    (cycleGraph 5).maxDegree = 2 ∧
      (strongChromaticIndex (cycleGraph 5) : ℝ) = (5 / 4 : ℝ) * ((cycleGraph 5).maxDegree : ℝ) ^ 2 := by
  have h2 : (cycleGraph 5).maxDegree = 2 := by decide
  refine ⟨h2, ?_⟩
  rw [erdos_problem_149.variants.c5_strongChromaticIndex, h2]
  norm_num

/-- The blow-up of `C₅` in which every vertex is replaced by `k` independent vertices, and two vertices are
adjacent when their classes are adjacent in `C₅` (the lexicographic product of `C₅` with the edgeless graph on
`k` vertices). Its maximum degree is `2 * k`. -/
def erdos_problem_149.blowupC5 (k : ℕ) : SimpleGraph (Fin 5 × Fin k) :=
  (cycleGraph 5).comap Prod.fst

/-- Adjacency in the blow-up of `C₅` is decidable, since it is adjacency of the classes in `C₅`. -/
instance (k : ℕ) : DecidableRel (erdos_problem_149.blowupC5 k).Adj :=
  fun p q => inferInstanceAs (Decidable ((cycleGraph 5).Adj p.1 q.1))

/-- In the blow-up of `C₅`, every two edges (distinct or not) have an endpoint of one adjacent to an endpoint of
the other (PROVED in Lean). -/
theorem erdos_problem_149.blowupC5_close (k : ℕ) :
    ∀ e₁ e₂ : (erdos_problem_149.blowupC5 k).edgeSet, e₁ ≠ e₂ →
      ∃ u ∈ (e₁ : Sym2 (Fin 5 × Fin k)), ∃ v ∈ (e₂ : Sym2 (Fin 5 × Fin k)),
        u = v ∨ (erdos_problem_149.blowupC5 k).Adj u v := by
  have key : ∀ a₁ b₁ a₂ b₂ : Fin 5, (cycleGraph 5).Adj a₁ b₁ → (cycleGraph 5).Adj a₂ b₂ →
      (cycleGraph 5).Adj a₁ a₂ ∨ (cycleGraph 5).Adj a₁ b₂ ∨ (cycleGraph 5).Adj b₁ a₂ ∨
        (cycleGraph 5).Adj b₁ b₂ := by
    decide
  intro e₁ e₂ _
  obtain ⟨e₁, h₁⟩ := e₁
  obtain ⟨e₂, h₂⟩ := e₂
  induction e₁ using Sym2.ind with
  | _ p₁ q₁ =>
  induction e₂ using Sym2.ind with
  | _ p₂ q₂ =>
  rw [SimpleGraph.mem_edgeSet] at h₁ h₂
  rcases key _ _ _ _ h₁ h₂ with h | h | h | h
  · exact ⟨p₁, Sym2.mem_mk_left _ _, p₂, Sym2.mem_mk_left _ _, Or.inr h⟩
  · exact ⟨p₁, Sym2.mem_mk_left _ _, q₂, Sym2.mem_mk_right _ _, Or.inr h⟩
  · exact ⟨q₁, Sym2.mem_mk_right _ _, p₂, Sym2.mem_mk_left _ _, Or.inr h⟩
  · exact ⟨q₁, Sym2.mem_mk_right _ _, q₂, Sym2.mem_mk_right _ _, Or.inr h⟩

/-- Every vertex of the blow-up of `C₅` has degree `2 * k` (PROVED in Lean). -/
theorem erdos_problem_149.blowupC5_degree (k : ℕ) (p : Fin 5 × Fin k) :
    (erdos_problem_149.blowupC5 k).degree p = 2 * k := by
  have h : (erdos_problem_149.blowupC5 k).neighborFinset p =
      (cycleGraph 5).neighborFinset p.1 ×ˢ (Finset.univ : Finset (Fin k)) := by
    ext q
    simp [SimpleGraph.mem_neighborFinset, erdos_problem_149.blowupC5]
  have h2 : ((cycleGraph 5).neighborFinset p.1).card = 2 := by
    have : ∀ a : Fin 5, ((cycleGraph 5).neighborFinset a).card = 2 := by decide
    exact this p.1
  rw [← SimpleGraph.card_neighborFinset_eq_degree, h, Finset.card_product, h2]
  simp

/-- The blow-up of `C₅` has `5 * k ^ 2` edges (PROVED in Lean, by the degree-sum formula). -/
theorem erdos_problem_149.blowupC5_card_edges (k : ℕ) :
    (erdos_problem_149.blowupC5 k).edgeFinset.card = 5 * k ^ 2 := by
  have := SimpleGraph.sum_degrees_eq_twice_card_edges (erdos_problem_149.blowupC5 k)
  simp only [erdos_problem_149.blowupC5_degree] at this
  have h : 2 * (erdos_problem_149.blowupC5 k).edgeFinset.card = 2 * (5 * k ^ 2) := by
    rw [← this]
    simp
    ring
  omega

/-- The blow-up of `C₅` has maximum degree `2 * k` when `k` is positive (PROVED in Lean). -/
theorem erdos_problem_149.blowupC5_maxDegree (k : ℕ) (hk : 0 < k) :
    (erdos_problem_149.blowupC5 k).maxDegree = 2 * k := by
  apply le_antisymm
  · exact SimpleGraph.maxDegree_le_of_forall_degree_le _ _
      (fun v => (erdos_problem_149.blowupC5_degree k v).le)
  · have := SimpleGraph.degree_le_maxDegree (erdos_problem_149.blowupC5 k) (0, ⟨0, hk⟩)
    rwa [erdos_problem_149.blowupC5_degree] at this

/--
The blow-ups of `C₅` meet the bound with equality for every even maximum degree (PROVED in Lean): the blow-up has
`Δ = 2 * k` and `χ'_s = 5 * k ^ 2 = 5 / 4 * Δ ^ 2`. This is the page's "this bound would be the best possible, as
witnessed by a blowup of `C₅`", and shows that the constant `5 / 4` of the main theorem cannot be lowered.
-/
theorem erdos_problem_149.variants.blowup_sharp (k : ℕ) (hk : 0 < k) :
    (erdos_problem_149.blowupC5 k).maxDegree = 2 * k ∧
      (strongChromaticIndex (erdos_problem_149.blowupC5 k) : ℝ) =
        (5 / 4 : ℝ) * ((erdos_problem_149.blowupC5 k).maxDegree : ℝ) ^ 2 := by
  have hmax := erdos_problem_149.blowupC5_maxDegree k hk
  refine ⟨hmax, ?_⟩
  have hcard : Fintype.card (erdos_problem_149.blowupC5 k).edgeSet = 5 * k ^ 2 := by
    rw [← erdos_problem_149.blowupC5_card_edges]
    simp [SimpleGraph.edgeFinset]
  rw [erdos_problem_149.variants.strongChromaticIndex_eq_card_of_close _
    (erdos_problem_149.blowupC5_close k), hcard, hmax]
  push_cast
  ring

/-- A set `S` of edges of `G` in which any two distinct edges are *not* strongly independent: they share a vertex
or an edge of `G` joins them. The largest such set is the clique number of `L(G)²`. -/
def IsCloseEdgeSet {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V)) : Prop :=
  S ⊆ G.edgeSet ∧ ∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → ∃ u ∈ e₁, ∃ v ∈ e₂, u = v ∨ G.Adj u v

/-- A set of pairwise close edges has at most `χ'_s(G)` elements (PROVED in Lean): their colours are distinct. -/
theorem erdos_problem_149.variants.clique_le_strongChromaticIndex {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset (Sym2 V))
    (hS : IsCloseEdgeSet G (S : Set (Sym2 V))) : S.card ≤ strongChromaticIndex G := by
  have hne : {k : ℕ | ∃ (c : G.edgeSet → Fin k), ∀ (e₁ e₂ : G.edgeSet), c e₁ = c e₂ → e₁ ≠ e₂ →
      ∀ u ∈ (e₁ : Sym2 V), ∀ v ∈ (e₂ : Sym2 V), u ≠ v ∧ ¬G.Adj u v}.Nonempty := by
    refine ⟨Fintype.card G.edgeSet, ?_⟩
    refine ⟨fun e => (Fintype.equivFin G.edgeSet) e, ?_⟩
    intro e₁ e₂ h hne
    exact absurd ((Fintype.equivFin G.edgeSet).injective h) hne
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  let f : S → Fin (strongChromaticIndex G) := fun e => c ⟨e.1, hS.1 (Finset.mem_coe.mpr e.2)⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    by_contra hne
    have hne' : (e₁ : Sym2 V) ≠ (e₂ : Sym2 V) := fun h' => hne (Subtype.ext h')
    obtain ⟨u, hu, v, hv, huv⟩ :=
      hS.2 e₁.1 (Finset.mem_coe.mpr e₁.2) e₂.1 (Finset.mem_coe.mpr e₂.2) hne'
    have hne'' : (⟨e₁.1, hS.1 (Finset.mem_coe.mpr e₁.2)⟩ : G.edgeSet) ≠
        ⟨e₂.1, hS.1 (Finset.mem_coe.mpr e₂.2)⟩ := fun h' => hne' (Subtype.mk.inj h')
    have := hc _ _ h hne'' u hu v hv
    rcases huv with h1 | h1
    · exact this.1 h1
    · exact this.2 h1
  have := Fintype.card_le_of_injective f hf
  simpa using this

/-- The bound `ω(L(G)²) ≤ c * Δ²` for the clique number of the square of the line graph. -/
def CliqueBound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : ℝ) : Prop :=
  ∀ S : Finset (Sym2 V), IsCloseEdgeSet G (S : Set (Sym2 V)) →
    (S.card : ℝ) ≤ c * (G.maxDegree : ℝ) ^ 2

/--
The main theorem implies the clique-number question (PROVED in Lean): `ω(L(G)²) ≤ χ'_s(G) ≤ (5/4) Δ²`.
-/
theorem erdos_problem_149.variants.clique_conjecture_of_main.{u}
    (hmain : ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (strongChromaticIndex G : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2)
    (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    CliqueBound G (5 / 4) := by
  intro S hS
  have h1 : (S.card : ℝ) ≤ (strongChromaticIndex G : ℝ) := by
    exact_mod_cast erdos_problem_149.variants.clique_le_strongChromaticIndex G S hS
  exact le_trans h1 (hmain V G)

/--
The page's open question (OPEN): is the clique number of `L(G)²` at most `5/4 * Δ ^ 2`?
-/
theorem erdos_problem_149.variants.clique_conjecture.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      CliqueBound G (5 / 4) :=
  sorry

/-- Śleszyńska-Nowak [Sl16] (PROVED, not checked here): `ω(L(G)²) ≤ 3/2 * Δ ^ 2`. -/
theorem erdos_problem_149.variants.sleszynska_nowak.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      CliqueBound G (3 / 2) :=
  sorry

/-- Faron and Postle [FaPo19] (PROVED, not checked here): `ω(L(G)²) ≤ 4/3 * Δ ^ 2`. -/
theorem erdos_problem_149.variants.faron_postle.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      CliqueBound G (4 / 3) :=
  sorry

/-- Cames van Batenburg, Kang and Pirot [CKP20] (PROVED, not checked here): `ω(L(G)²) ≤ 5/4 * Δ ^ 2` for
triangle-free `G`. -/
theorem erdos_problem_149.variants.ckp_triangle_free.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.CliqueFree 3 → CliqueBound G (5 / 4) :=
  sorry

/-- Cames van Batenburg, Kang and Pirot [CKP20] (PROVED, not checked here): `ω(L(G)²) ≤ Δ ^ 2` if `G` has no
`C₅` subgraph. -/
theorem erdos_problem_149.variants.ckp_c5_free.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (cycleGraph 5).Free G → CliqueBound G 1 :=
  sorry

/--
Chung, Gyárfás, Tuza and Trotter [CGTT90] (PROVED, not checked here): a graph in which any two distinct edges are
not strongly independent has at most `5/4 * Δ ^ 2` edges.
-/
theorem erdos_problem_149.variants.cgtt.{u} :
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      IsCloseEdgeSet G G.edgeSet → (G.edgeFinset.card : ℝ) ≤ (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 :=
  sorry

/--
The page's wording of [CGTT90], "at least `5/4 * Δ ^ 2` edges implies two strongly independent edges", is false at
`C₅` (PROVED in Lean): `C₅` has `5 = 5/4 * 2 ^ 2` edges and no two strongly independent edges. The theorem needs
"more than" in place of "at least", or the form `variants.cgtt`.
-/
theorem erdos_problem_149.variants.page_wording_of_cgtt_false :
    ¬ (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (5 / 4 : ℝ) * (G.maxDegree : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
      ∃ e₁ ∈ G.edgeSet, ∃ e₂ ∈ G.edgeSet, e₁ ≠ e₂ ∧
        ∀ u ∈ e₁, ∀ v ∈ e₂, u ≠ v ∧ ¬G.Adj u v) := by
  intro h
  have hclose : ∀ e₁ e₂ : (cycleGraph 5).edgeSet, e₁ ≠ e₂ →
      ∃ u ∈ (e₁ : Sym2 (Fin 5)), ∃ v ∈ (e₂ : Sym2 (Fin 5)), u = v ∨ (cycleGraph 5).Adj u v := by
    decide
  have hdeg : (cycleGraph 5).maxDegree = 2 := by decide
  have hedges : (cycleGraph 5).edgeFinset.card = 5 := by decide
  obtain ⟨e₁, he₁, e₂, he₂, hne, hind⟩ := h (Fin 5) (cycleGraph 5) (by
    rw [hdeg, hedges]
    norm_num)
  obtain ⟨u, hu, v, hv, huv⟩ := hclose ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ (fun h' => hne (congrArg Subtype.val h'))
  have := hind u hu v hv
  rcases huv with h1 | h1
  · exact this.1 h1
  · exact this.2 h1

/-- The bound `χ'_s(G) ≤ c * Δ ^ 2` for every graph whose maximum degree is large enough. -/
def StrongBound.{u} (c : ℝ) : Prop :=
  ∃ Δ₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    Δ₀ ≤ G.maxDegree → (strongChromaticIndex G : ℝ) ≤ c * (G.maxDegree : ℝ) ^ 2

/-- A bound with a smaller constant gives the bound with a larger constant (PROVED in Lean). -/
theorem erdos_problem_149.variants.StrongBound_mono.{u} {c c' : ℝ} (h : StrongBound.{u} c)
    (hcc : c ≤ c') : StrongBound.{u} c' := by
  obtain ⟨Δ₀, hΔ⟩ := h
  refine ⟨Δ₀, fun V _ _ G _ hd => ?_⟩
  refine le_trans (hΔ V G hd) ?_
  exact mul_le_mul_of_nonneg_right hcc (sq_nonneg _)

/-- Molloy and Reed [MoRe97] (PROVED, not checked here): `1.998 * Δ ^ 2` colours suffice for large `Δ`. -/
theorem erdos_problem_149.variants.molloy_reed.{u} : StrongBound.{u} (1998 / 1000) :=
  sorry

/-- Bruhn and Joos [BrJo18] (PROVED, not checked here): `1.93 * Δ ^ 2`. -/
theorem erdos_problem_149.variants.bruhn_joos.{u} : StrongBound.{u} (193 / 100) :=
  sorry

/-- Bonamy, Perrett and Postle [BPP22] (PROVED, not checked here): `1.835 * Δ ^ 2`. -/
theorem erdos_problem_149.variants.bonamy_perrett_postle.{u} : StrongBound.{u} (1835 / 1000) :=
  sorry

/-- Hurley, de Joannis de Verclos and Kang [HJK22] (PROVED, not checked here): `1.772 * Δ ^ 2`, the best bound
on the page. -/
theorem erdos_problem_149.variants.hurley_de_verclos_kang.{u} : StrongBound.{u} (1772 / 1000) :=
  sorry

/-- The weaker conjecture, "some `c > 0` with `(2 - c) * Δ ^ 2` colours suffice", follows from [MoRe97] with
`c = 0.002` (PROVED in Lean from `molloy_reed`). -/
theorem erdos_problem_149.variants.weaker_conjecture.{u} (h : StrongBound.{u} (1998 / 1000)) :
    ∃ c : ℝ, 0 < c ∧ StrongBound.{u} (2 - c) := by
  refine ⟨1 / 500, by norm_num, ?_⟩
  have : (2 : ℝ) - 1 / 500 = 1998 / 1000 := by norm_num
  rw [this]
  exact h

/-- Mahdian's Masters' thesis (PROVED, not checked here): for `C₄`-free `G`, `χ'_s(G) ≤ (2 + o(1)) * Δ ^ 2 / log Δ`. -/
theorem erdos_problem_149.variants.mahdian.{u} :
    ∀ ε : ℝ, 0 < ε → ∃ Δ₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (cycleGraph 4).Free G → Δ₀ ≤ G.maxDegree →
        (strongChromaticIndex G : ℝ) ≤ (2 + ε) * (G.maxDegree : ℝ) ^ 2 / Real.log (G.maxDegree : ℝ) :=
  sorry
