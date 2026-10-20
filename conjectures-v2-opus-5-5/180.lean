-- [AI - Claude Opus 5.5]: Erdős Problem 180 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Archimedean
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Erdős Problem #180

*Source:* [erdosproblems.com/180](https://www.erdosproblems.com/180) (status **OPEN** at capture: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-20; page edited 18
January 2026). [ErSi82]

If $\mathcal{F}$ is a finite set of finite graphs then $\mathrm{ex}(n;\mathcal{F})$ is the maximum
number of edges a graph on $n$ vertices can have without containing any subgraphs from
$\mathcal{F}$. Note that it is trivial that $\mathrm{ex}(n;\mathcal{F})\leq \mathrm{ex}(n;G)$ for
every $G\in\mathcal{F}$. Is it true that, for every $\mathcal{F}$, there exists
$G\in\mathcal{F}$ such that $\mathrm{ex}(n;G)\ll_{\mathcal{F}}\mathrm{ex}(n;\mathcal{F})$?

Remarks recorded on the page: a problem of Erdős and Simonovits. This is trivially true if
$\mathcal{F}$ does not contain any bipartite graphs, by the Erdős–Stone theorem. Erdős and
Simonovits observe that this is false for infinite families $\mathcal{F}$, e.g. the family of all
cycles. Hunter has provided the following 'folklore counterexample': if $\mathcal{F}=\{H_1,H_2\}$
where $H_1$ is a star and $H_2$ is a matching, both with at least two edges, then
$\mathrm{ex}(n;\mathcal{F})\ll 1$, but $\mathrm{ex}(n;H_i)\asymp n$ for $1\leq i\leq 2$. This
conjecture may still hold for all other $\mathcal{F}$. See also [575]. This problem is #47 in
Extremal Graph Theory in the graphs problem collection.

After the capture, the mirror (`b916d95`) records `disproved (Lean)` (2026-08-02, "counterexample;
refutes the compactness conjecture"), and upstream `formal-conjectures` (`df3f12d`) states that the
answer is no even for families with no acyclic member, citing [OpenAI26]
(`variants.cyclic_counterexample`). Neither proof was examined here.

## Encoding notes

* The question as stated has answer **no**: Hunter's family `{star2, match2}` is a counterexample.
  The input asserted the "yes" answer, although its own docstring records the counterexample.
  v2's main theorem is the negation, PROVED in Lean:
  - a graph with two distinct edges contains a two-edge star or two disjoint edges (`two_edges`),
    so `ex(n; {star2, match2}) ≤ 1` (`family_le_one`);
  - a matching on `2m` vertices avoids `star2` and has `m` edges, and a star on `m + 1` vertices
    avoids `match2` and has `m` edges (`matching_card`, `star_card`), so both single Turán numbers
    are unbounded.
* The open part ("this conjecture may still hold for all other $\mathcal{F}$") is not precise enough
  for a formal target.
* `turanNumber180` and `turanNumberFamily180` are `sSup` of edge counts of `H`-free graphs on `n`
  vertices. The sets are bounded by `n.choose 2`; they are empty (junk value `0`) only when some
  forbidden graph has no edges and at most `n` vertices.

## References

* [ErSi82] Erdős, P. and Simonovits, M., _Compactness results in extremal graph theory_.
  Combinatorica (1982), 275–288. (**DEFERRED:** from upstream's docstring; the site's
  `/latex/180` lists no bibliography entry.)
* [OpenAI26] OpenAI, _Ten advances in mathematics and theoretical computer science_ (2026). (From
  upstream; after the capture.)

*Provenance:* second pass of `conjectures/180.lean` (Opus 5.5 review, `opus-5-5-review/180.md`). The
input's theorem asserted the refuted "yes" answer; it is replaced by its negation.
-/

open SimpleGraph

noncomputable section

/-- An injective graph homomorphism from H to G: G contains a copy of H as a subgraph. -/
def containsSubgraph180 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber180 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph180 F H ∧ F.edgeFinset.card = m}

/-- The Turán number for a family ex(n; F): the maximum number of edges in a simple
    graph on n vertices that contains no copy of any member of the family F as a
    subgraph. The family is given as a function from a finite index type ι to finite
    graphs SimpleGraph (Fin (k i)). -/
noncomputable def turanNumberFamily180
    {ι : Type*} [Fintype ι]
    {k : ι → ℕ} (H : (i : ι) → SimpleGraph (Fin (k i))) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ (∀ i : ι, ¬containsSubgraph180 F (H i)) ∧ F.edgeFinset.card = m}

/-- Hunter's first graph: the star with two edges, centre `0`. -/
def erdos_problem_180.star2 : SimpleGraph (Fin 3) := SimpleGraph.fromRel (fun a b => a = 0 ∧ b ≠ 0)

/-- Hunter's second graph: two disjoint edges `01`, `23`. -/
def erdos_problem_180.match2 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun a b => (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 3))

/-- A graph with two distinct edges contains `star2` (if they share a vertex) or `match2` (if
not) (PROVED in Lean). -/
theorem erdos_problem_180.two_edges {V : Type*} (G : SimpleGraph V) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) (hne : s(a, b) ≠ s(c, d)) :
    containsSubgraph180 G erdos_problem_180.star2 ∨ containsSubgraph180 G erdos_problem_180.match2 := by
  have hab' := G.ne_of_adj hab
  have hcd' := G.ne_of_adj hcd
  -- a star with centre x and leaves y, z
  have mkstar : ∀ x y z : V, G.Adj x y → G.Adj x z → y ≠ z → containsSubgraph180 G erdos_problem_180.star2 := by
    intro x y z hxy hxz hyz
    have hxy' := G.ne_of_adj hxy
    have hxz' := G.ne_of_adj hxz
    refine ⟨![x, y, z], ?_, ?_⟩
    · intro p q hpq
      fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
    · intro p q hpq
      simp only [erdos_problem_180.star2, SimpleGraph.fromRel_adj] at hpq
      fin_cases p <;> fin_cases q <;> simp_all [G.symm hxy, G.symm hxz]
  by_cases h1 : a = c
  · subst h1
    exact Or.inl (mkstar a b d hab hcd (fun h => hne (by rw [h])))
  by_cases h2 : a = d
  · subst h2
    exact Or.inl (mkstar a b c hab (G.symm hcd) (fun h => hne (by rw [h, Sym2.eq_swap])))
  by_cases h3 : b = c
  · subst h3
    exact Or.inl (mkstar b a d (G.symm hab) hcd (fun h => hne (by rw [h, Sym2.eq_swap])))
  by_cases h4 : b = d
  · subst h4
    exact Or.inl (mkstar b a c (G.symm hab) (G.symm hcd) (fun h => hne (by rw [h])))
  right
  refine ⟨![a, b, c, d], ?_, ?_⟩
  · intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [eq_comm]
  · intro p q hpq
    simp only [erdos_problem_180.match2, SimpleGraph.fromRel_adj] at hpq
    fin_cases p <;> fin_cases q <;> simp_all <;>
      first | exact hab | exact hcd | exact G.symm hab | exact G.symm hcd


/-- A graph avoiding both `star2` and `match2` has at most one edge (PROVED in Lean). -/
theorem erdos_problem_180.card_le_one_of_avoid {V : Type} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (h1 : ¬containsSubgraph180 F erdos_problem_180.star2) (h2 : ¬containsSubgraph180 F erdos_problem_180.match2) :
    F.edgeFinset.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  by_contra hne
  rw [SimpleGraph.mem_edgeFinset] at he₁ he₂
  induction e₁ using Sym2.ind with
  | h a b =>
    induction e₂ using Sym2.ind with
    | h c d =>
      rcases erdos_problem_180.two_edges F he₁ he₂ hne with h | h
      · exact h1 h
      · exact h2 h

/-- Vertex counts of Hunter's family: `3` (the star) and `4` (the matching). -/
def erdos_problem_180.hunterSizes : Bool → ℕ := fun b => Bool.rec 3 4 b

/-- Hunter's family `{star2, match2}`, indexed by `Bool`. -/
def erdos_problem_180.hunterFamily : (b : Bool) → SimpleGraph (Fin (erdos_problem_180.hunterSizes b)) :=
  fun b => Bool.rec (motive := fun b => SimpleGraph (Fin (erdos_problem_180.hunterSizes b))) erdos_problem_180.star2 erdos_problem_180.match2 b

/-- `ex(n; {star2, match2}) ≤ 1` for every `n` (PROVED in Lean). -/
theorem erdos_problem_180.family_le_one (n : ℕ) : turanNumberFamily180 erdos_problem_180.hunterFamily n ≤ 1 := by
  apply csSup_le'
  rintro m ⟨V, fv, F, dr, -, havoid, rfl⟩
  exact @erdos_problem_180.card_le_one_of_avoid V fv F dr (havoid false) (havoid true)

/-- Any `H`-free graph on `n` vertices bounds `ex(n; H)` from below (PROVED in Lean). -/
theorem erdos_problem_180.turan_ge {U : Type*} (H : SimpleGraph U) (n : ℕ) {V : Type} [Fintype V]
    (F : SimpleGraph V) [DecidableRel F.Adj] (hn : Fintype.card V = n)
    (hF : ¬containsSubgraph180 F H) : F.edgeFinset.card ≤ turanNumber180 H n := by
  apply le_csSup
  · refine ⟨n.choose 2, ?_⟩
    rintro m ⟨V', fv, F', dr, hc, -, rfl⟩
    rw [← hc]
    exact SimpleGraph.card_edgeFinset_le_card_choose_two
  · exact ⟨V, inferInstance, F, inferInstance, hn, hF, rfl⟩

/-- The perfect matching `{2j, 2j + 1}` on `Fin (2m)`. -/
def erdos_problem_180.matchingGraph (m : ℕ) : SimpleGraph (Fin (2 * m)) :=
  SimpleGraph.fromRel (fun i j => (i : ℕ) / 2 = (j : ℕ) / 2)

/-- Decidability of adjacency in `matchingGraph` (for `edgeFinset`). -/
instance erdos_problem_180.decMatching (m : ℕ) : DecidableRel (erdos_problem_180.matchingGraph m).Adj := by
  unfold erdos_problem_180.matchingGraph; infer_instance

/-- A matching contains no two-edge star (PROVED in Lean). -/
theorem erdos_problem_180.matching_avoids (m : ℕ) : ¬containsSubgraph180 (erdos_problem_180.matchingGraph m) erdos_problem_180.star2 := by
  rintro ⟨f, hf, hadj⟩
  have h1 := hadj 0 1 (by simp [erdos_problem_180.star2, SimpleGraph.fromRel_adj])
  have h2 := hadj 0 2 (by simp [erdos_problem_180.star2, SimpleGraph.fromRel_adj])
  simp only [erdos_problem_180.matchingGraph, SimpleGraph.fromRel_adj] at h1 h2
  have h12 : f 1 ≠ f 2 := fun h => absurd (hf h) (by decide)
  have a1 := Fin.val_injective.ne h1.1
  have a2 := Fin.val_injective.ne h2.1
  have a3 := Fin.val_injective.ne h12
  omega

/-- `matchingGraph m` has at least `m` edges (PROVED in Lean). -/
theorem erdos_problem_180.matching_card (m : ℕ) : m ≤ (erdos_problem_180.matchingGraph m).edgeFinset.card := by
  let g : Fin m → Sym2 (Fin (2 * m)) := fun j => s(⟨2 * j, by omega⟩, ⟨2 * j + 1, by omega⟩)
  have hinj : Function.Injective g := by
    intro j j' h
    simp only [g, Sym2.eq_iff, Fin.ext_iff] at h
    ext; omega
  have hsub : Finset.univ.image g ⊆ (erdos_problem_180.matchingGraph m).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨j, -, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    simp only [erdos_problem_180.matchingGraph, SimpleGraph.fromRel_adj, ne_eq, Fin.ext_iff]
    omega
  calc m = (Finset.univ : Finset (Fin m)).card := by simp
    _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The star with centre `0` on `Fin (m + 1)`. -/
def erdos_problem_180.starGraph (m : ℕ) : SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel (fun i _ => i = 0)

/-- Decidability of adjacency in `starGraph` (for `edgeFinset`). -/
instance erdos_problem_180.decStar (m : ℕ) : DecidableRel (erdos_problem_180.starGraph m).Adj := by
  unfold erdos_problem_180.starGraph; infer_instance

/-- A star contains no two disjoint edges (PROVED in Lean). -/
theorem erdos_problem_180.star_avoids (m : ℕ) : ¬containsSubgraph180 (erdos_problem_180.starGraph m) erdos_problem_180.match2 := by
  rintro ⟨f, hf, hadj⟩
  have h1 := hadj 0 1 (by simp [erdos_problem_180.match2, SimpleGraph.fromRel_adj])
  have h2 := hadj 2 3 (by simp [erdos_problem_180.match2, SimpleGraph.fromRel_adj])
  simp only [erdos_problem_180.starGraph, SimpleGraph.fromRel_adj] at h1 h2
  have i02 : f 0 ≠ f 2 := fun h => absurd (hf h) (by decide)
  have i03 : f 0 ≠ f 3 := fun h => absurd (hf h) (by decide)
  have i12 : f 1 ≠ f 2 := fun h => absurd (hf h) (by decide)
  have i13 : f 1 ≠ f 3 := fun h => absurd (hf h) (by decide)
  rcases h1.2 with h | h <;> rcases h2.2 with h' | h' <;> simp_all

/-- `starGraph m` has at least `m` edges (PROVED in Lean). -/
theorem erdos_problem_180.star_card (m : ℕ) : m ≤ (erdos_problem_180.starGraph m).edgeFinset.card := by
  let g : Fin m → Sym2 (Fin (m + 1)) := fun j => s(0, ⟨j + 1, by omega⟩)
  have hinj : Function.Injective g := by
    intro j j' h
    simp only [g, Sym2.eq_iff, Fin.ext_iff, Fin.val_zero] at h
    ext; omega
  have hsub : Finset.univ.image g ⊆ (erdos_problem_180.starGraph m).edgeFinset := by
    intro e he
    rw [Finset.mem_image] at he
    obtain ⟨j, -, rfl⟩ := he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    show (erdos_problem_180.starGraph m).Adj 0 ⟨j + 1, by omega⟩
    rw [erdos_problem_180.starGraph, SimpleGraph.fromRel_adj]
    refine ⟨fun h => ?_, Or.inl rfl⟩
    have := congrArg Fin.val h
    simp at this
  calc m = (Finset.univ : Finset (Fin m)).card := by simp
    _ = (Finset.univ.image g).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ _ := Finset.card_le_card hsub

/--
Erdős Problem #180 [ErSi82], second pass: the answer to the question as stated is **no**
(PROVED in Lean). For Hunter's family `{star2, match2}`, `ex(n; F) ≤ 1` while `ex(n; star2)` and
`ex(n; match2)` are unbounded, so no member satisfies `ex(n; G) ≤ C · ex(n; F)` for all `n ≥ 1`.
The input asserted the statement below without the negation.
-/
theorem erdos_problem_180 :
    ¬ (∀ (ι : Type) [Fintype ι] [Nonempty ι]
      (k : ι → ℕ) (H : (i : ι) → SimpleGraph (Fin (k i))),
    ∃ i : ι,
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (turanNumber180 (H i) n : ℝ) ≤ C * (turanNumberFamily180 H n : ℝ)) := by
  intro h
  obtain ⟨i, C, hC, hb⟩ := h Bool erdos_problem_180.hunterSizes erdos_problem_180.hunterFamily
  obtain ⟨m, hm⟩ := exists_nat_gt C
  have key : ∀ n : ℕ, 1 ≤ n → (m : ℝ) + 1 ≤ (turanNumber180 (erdos_problem_180.hunterFamily i) n : ℝ) → False := by
    intro n hn hlow
    have h1 := hb n hn
    have hfam : (turanNumberFamily180 erdos_problem_180.hunterFamily n : ℝ) ≤ 1 := by exact_mod_cast erdos_problem_180.family_le_one n
    have : C * (turanNumberFamily180 erdos_problem_180.hunterFamily n : ℝ) ≤ C := mul_le_of_le_one_right hC.le hfam
    linarith
  cases i with
  | false =>
    apply key (2 * (m + 1)) (by omega)
    have := le_trans (erdos_problem_180.matching_card (m + 1))
      (erdos_problem_180.turan_ge erdos_problem_180.star2 (2 * (m + 1)) (erdos_problem_180.matchingGraph (m + 1)) (by simp) (erdos_problem_180.matching_avoids _))
    exact_mod_cast this
  | true =>
    apply key (m + 1 + 1) (by omega)
    have := le_trans (erdos_problem_180.star_card (m + 1))
      (erdos_problem_180.turan_ge erdos_problem_180.match2 (m + 1 + 1) (erdos_problem_180.starGraph (m + 1)) (by simp) (erdos_problem_180.star_avoids _))
    exact_mod_cast this

/-- [OpenAI26], as recorded by upstream (SOLVED after the capture; not proved here): even
families in which no member is acyclic can fail the property. -/
theorem erdos_problem_180.variants.cyclic_counterexample :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (k : ι → ℕ)
      (H : (i : ι) → SimpleGraph (Fin (k i))),
      (∀ i, ¬ (H i).IsAcyclic) ∧
      ¬ ∃ i : ι, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber180 (H i) n : ℝ) ≤ C * (turanNumberFamily180 H n : ℝ) :=
  sorry

end
