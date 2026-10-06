-- [AI - Claude Sonnet 5.5]: Erdős Problem 147 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open SimpleGraph
open Filter

/-!
# Erdős Problem #147: Turán numbers of bipartite graphs with minimum degree $r$ (DISPROVED)

*Source:* [erdosproblems.com/147](https://www.erdosproblems.com/147) (banner **DISPROVED**, prize **\$500**:
"This has been solved in the negative."; page last edited 18 January 2026; captured 2026-02-20 as the page and as
the tidied problem box, with identical content). [ErSi84] [Er93] [Er97c]

If $H$ is bipartite with minimum degree $r$ then there exists $\epsilon=\epsilon(H)>0$ such that
$\mathrm{ex}(n;H) \gg n^{2-\frac{1}{r-1}+\epsilon}$.

Remarks recorded on the page:
* Conjectured by Erdős and Simonovits [ErSi84]. A probabilistic argument shows that there exists some
  $\epsilon=\epsilon(H)>0$ such that $\mathrm{ex}(n;H) \gg n^{2-\frac{2}{r}+\epsilon}$.
* This conjecture was disproved by Janzer [Ja23] for even $r\geq 4$. The case $r=3$ was disproved by Janzer
  [Ja23b], who constructed, for any $\epsilon>0$, a $3$-regular bipartite graph $H$ such that
  $\mathrm{ex}(n;H)\ll n^{\frac{4}{3}+\epsilon}$.
* In [Ja23] Janzer conjectures that the above lower bound is sharp, in that for any $r\geq 3$ and $\epsilon>0$
  there exists an $r$-regular graph $H$ such that $\mathrm{ex}(n;H) \ll n^{2-\frac{2}{r}+\epsilon}$. Janzer's
  result proves this for even $r\geq 4$.
* See also [113], [146] and [714]. This problem is #44 in Extremal Graph Theory in the graphs problem
  collection.

Tags: graph theory, turán number. 1 comment at capture (not captured).

**Status.** DISPROVED. The mirror (`teorth/erdosproblems`) has `disproved` since 2025-08-31 and
`disproved (Lean)` since 2026-08-24, prize \$500. Upstream has `erdos_147 : answer(False) ↔ …`, category
`research solved`, with a formal-proof link (`plby/lean-proofs`), and the variants `janzer_even`, `cubic` and
`janzer_conjecture` (the last `research open`).

**What the first pass got wrong, and what this file does.**
* *The polarity.* The first pass asserts the conjecture, although its own docstring says "This conjecture was
  DISPROVED". v2 asserts the negation.
* *A second defect, independent of Janzer.* The first pass's statement is **false for a trivial reason**: for the
  graph on no vertices the hypotheses hold vacuously (it is bipartite, and every vertex has degree at least `r`),
  every graph contains it, so `turanNumber147 H n = 0`, and no bound `C * n ^ … ≤ 0` with `C > 0` holds.
  `variants.first_pass_false` proves this in Lean. The page's "if $H$ is bipartite with minimum degree $r$"
  means a graph with vertices, so v2 adds `[Nonempty U]` to the main theorem, as upstream does. Without it a
  "disproof" of the first pass's statement would say nothing about Janzer's theorems.

**Encoding.**
* "Bipartite" is `Nonempty (H.Coloring (Fin 2))`. "Minimum degree $r$" is `∀ v, r ≤ H.degree v`, "at least
  $r$". This is equivalent for the universal statement: if the bound holds for every `H` with its exact minimum
  degree `d`, it holds for `r ≤ d` a fortiori, because the exponent $2-\frac1{r-1}$ increases with `r`, and
  taking `r = d` recovers the page's form. The condition `2 ≤ r` is needed for the exponent to be defined.
* "$\gg$" is `∃ ε > 0, ∃ C > 0, ∃ N₀, ∀ n ≥ N₀, C * n ^ (2 - 1/(r-1) + ε) ≤ ex(n; H)`, with `ε` depending on `H`.
* `turanNumber147 H n` is the maximum number of edges of an `n`-vertex graph with no copy of `H`.
  `variants.containsSubgraph_iff` and `variants.turanNumber_eq_extremalNumber` show that it is built from
  Mathlib's `H ⊑ F` and equals `SimpleGraph.extremalNumber n H`.
* `variants.cubic`, `variants.janzer_even` and `variants.janzer_conjecture` are the page's statements about
  Janzer's graphs. `variants.refutation_of_cubic` proves in Lean that `variants.cubic` implies the main theorem.
  `variants.probabilistic_lower_bound` is the page's probabilistic bound.
* The statements about Janzer's graphs are stated in an arbitrary universe, like the main theorem. A finite
  graph can be moved between universes by `ULift`.

## References

* [ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_. In: Progress in
  graph theory (Waterloo, Ont., 1982) (1984), 203–218.
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_. Quaestiones Math.
  (1993), 333–350.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [Ja23] Janzer, O., _Rainbow Turán number of even cycles, repeated patterns and blow-ups of cycles_. Israel J.
  Math. (2023), 813–840.
* [Ja23b] Janzer, O., _Disproof of a conjecture of Erdős and Simonovits on the Turán number of graphs with
  minimum degree 3_. Int. Math. Res. Not. IMRN (2023), 8478–8494.
* [113], [146], [714] The page's cross-references to Problems 113, 146 and 714.

(Provenance: [ErSi84], [Ja23] and [Ja23b] are from the `/latex/147` fetch in the session logs. [Er93] and
[Er97c] are from the bibliographies of the `/latex` pages of other problems.)
-/

/-- An injective graph homomorphism from H to F; witnesses that F contains a
    subgraph isomorphic to H. -/
def containsSubgraph147 {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber147 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph147 F H ∧ F.edgeFinset.card = m}

/--
Erdős Problem #147 [ErSi84] — DISPROVED (\$500):
If H is a bipartite graph with minimum degree r (i.e., every vertex of H has
degree at least r, where r ≥ 2), then there exists ε = ε(H) > 0 such that

  ex(n; H) ≫ n^{2 - 1/(r-1) + ε}

That is, there exist constants C > 0 and N₀ ∈ ℕ such that for all n ≥ N₀:
  ex(n; H) ≥ C · n^{2 - 1/(r-1) + ε}

This conjecture was DISPROVED: Janzer [Ja23] disproved it for even r ≥ 4, and
[Ja23b] disproved it for r = 3, constructing for any δ > 0 a 3-regular bipartite
graph H with ex(n; H) ≪ n^{4/3 + δ}. This file states the negation, for graphs with at least one vertex
(`[Nonempty U]`): the statement without it is false at the empty graph (`variants.first_pass_false`).
-/
theorem erdos_problem_147 :
    ¬ (∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [Nonempty U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (turanNumber147 H n : ℝ)) :=
  sorry

/--
The first pass's statement is false at the graph on no vertices (PROVED in Lean): the hypotheses hold
vacuously, every graph contains the empty graph, so `turanNumber147 H n = 0`, and `C * n ^ … ≤ 0` fails for
`C > 0` and `n ≥ 1`. This is independent of Janzer's theorems, and it is why the main theorem has `[Nonempty U]`.
-/
theorem erdos_problem_147.variants.first_pass_false.{u} :
    ¬ (∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type u) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (turanNumber147 H n : ℝ)) := by
  intro h
  let H : SimpleGraph PEmpty.{u + 1} := ⊥
  haveI : DecidableRel H.Adj := fun a _ => a.elim
  have hbip : Nonempty (H.Coloring (Fin 2)) :=
    ⟨⟨fun v => v.elim, fun {a} _ _ => a.elim⟩⟩
  obtain ⟨ε, hε, C, hC, N₀, hN⟩ := h 2 le_rfl PEmpty.{u + 1} H hbip (fun v => v.elim)
  have h0 : turanNumber147 H (N₀ + 1) = 0 := by
    unfold turanNumber147
    have hempty : {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V)
        (dr : DecidableRel F.Adj), haveI := fv; haveI := dr;
        Fintype.card V = N₀ + 1 ∧ ¬containsSubgraph147 F H ∧ F.edgeFinset.card = m} = ∅ := by
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨V, fv, F, dr, -, hF, -⟩
      exact hF ⟨fun x => x.elim, fun x => x.elim, fun u => u.elim⟩
    rw [hempty]
    exact csSup_empty
  have hle := hN (N₀ + 1) (Nat.le_succ N₀)
  rw [h0] at hle
  have hpos : 0 < C * (((N₀ + 1 : ℕ) : ℝ)) ^ ((2 : ℝ) - 1 / (((2 : ℕ) : ℝ) - 1) + ε) :=
    mul_pos hC (Real.rpow_pos_of_pos (by positivity) _)
  simp only [Nat.cast_zero] at hle
  linarith

/--
Janzer [Ja23b] (PROVED, not checked here): for every `ε > 0` there is a `3`-regular bipartite graph `H` with
`ex(n; H) ≪ n ^ (4 / 3 + ε)`. It is stated for a type in an arbitrary universe, as the main theorem is.
-/
theorem erdos_problem_147.variants.cubic.{u} :
    ∀ ε : ℝ, 0 < ε →
      ∃ (U : Type u) (_ : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (_ : DecidableRel H.Adj),
        Nonempty (H.Coloring (Fin 2)) ∧ (∀ v, H.degree v = 3) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (turanNumber147 H n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 + ε) :=
  sorry

/--
Janzer [Ja23] (PROVED, not checked here): for every even `r ≥ 4` and `ε > 0` there is an `r`-regular bipartite
graph `H` with `ex(n; H) ≪ n ^ (2 - 2 / r + ε)`.
-/
theorem erdos_problem_147.variants.janzer_even.{u} :
    ∀ r : ℕ, 4 ≤ r → Even r → ∀ ε : ℝ, 0 < ε →
      ∃ (U : Type u) (_ : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (_ : DecidableRel H.Adj),
        Nonempty (H.Coloring (Fin 2)) ∧ (∀ v, H.degree v = r) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (turanNumber147 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 2 / (r : ℝ) + ε) :=
  sorry

/--
Janzer's conjecture [Ja23] (OPEN, and PROVED for even `r ≥ 4`): for every `r ≥ 3` and `ε > 0` there is an
`r`-regular graph `H` with `ex(n; H) ≪ n ^ (2 - 2 / r + ε)`. The page says "an `r`-regular graph". Such an `H`
is bipartite, since a graph of chromatic number at least `3` has `ex(n; H) ≫ n ^ 2`.
-/
theorem erdos_problem_147.variants.janzer_conjecture.{u} :
    ∀ r : ℕ, 3 ≤ r → ∀ ε : ℝ, 0 < ε →
      ∃ (U : Type u) (_ : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (_ : DecidableRel H.Adj),
        (∀ v, H.degree v = r) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (turanNumber147 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 2 / (r : ℝ) + ε) :=
  sorry

/--
The page's probabilistic bound (PROVED by a probabilistic argument, not checked here): for bipartite `H` with
minimum degree at least `r ≥ 2`, `ex(n; H) ≫ n ^ (2 - 2 / r + ε)` for some `ε = ε(H) > 0`. For `r = 2` the exponent
equals the conjectured one, so the conjecture holds at `r = 2`. For `r ≥ 3` the exponent is smaller.
-/
theorem erdos_problem_147.variants.probabilistic_lower_bound :
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [Nonempty U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 2 / (r : ℝ) + ε) ≤ (turanNumber147 H n : ℝ) :=
  sorry

/--
Janzer's cubic graphs refute the conjecture (PROVED in Lean): with `ε = 1 / 12` the graph of `variants.cubic`
has `ex(n; H) ≤ C₁ * n ^ (17 / 12)`, while the conjecture at `r = 3` asks for `C * n ^ (3 / 2 + ε')` with
`ε' > 0` and `3 / 2 = 18 / 12`. Then `C * n ^ (1 / 12 + ε') ≤ C₁` for large `n`, which fails since the power
tends to infinity.
-/
theorem erdos_problem_147.variants.refutation_of_cubic.{u}
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ (U : Type u) (_ : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (_ : DecidableRel H.Adj),
        Nonempty (H.Coloring (Fin 2)) ∧ (∀ v, H.degree v = 3) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (turanNumber147 H n : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 + ε)) :
    ¬ (∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type u) (H : SimpleGraph U) [Fintype U] [Nonempty U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (turanNumber147 H n : ℝ)) := by
  intro hconj
  obtain ⟨U, fU, nU, H, dr, hbip, hreg, C₁, hC₁, hbd⟩ := h (1 / 12) (by norm_num)
  obtain ⟨ε, hε, C, hC, N₀, hN⟩ :=
    @hconj 3 (by norm_num) U H fU nU dr hbip (fun v => by rw [hreg v])
  have h2 : (2 : ℝ) - 1 / (((3 : ℕ) : ℝ) - 1) + ε = 17 / 12 + (1 / 12 + ε) := by
    push_cast
    ring
  rw [h2] at hN
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 12 + ε)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C₁ / C < (n : ℝ) ^ (1 / 12 + ε) :=
    htend.eventually_gt_atTop (C₁ / C)
  obtain ⟨n, h1, h2', h3⟩ := ((eventually_ge_atTop N₀).and (hlarge.and (eventually_ge_atTop 1))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h3
  have hlow := hN n h1
  have hup := hbd n h3
  have hexp : (4 : ℝ) / 3 + 1 / 12 = 17 / 12 := by norm_num
  rw [hexp] at hup
  rw [Real.rpow_add hnpos] at hlow
  have hpos : 0 < (n : ℝ) ^ ((17 : ℝ) / 12) := Real.rpow_pos_of_pos hnpos _
  have hle : C * (n : ℝ) ^ (1 / 12 + ε) ≤ C₁ := by
    have h4 : C * ((n : ℝ) ^ ((17 : ℝ) / 12) * (n : ℝ) ^ (1 / 12 + ε)) ≤
        C₁ * (n : ℝ) ^ ((17 : ℝ) / 12) := le_trans hlow hup
    have h5 : (C * (n : ℝ) ^ (1 / 12 + ε)) * (n : ℝ) ^ ((17 : ℝ) / 12) ≤
        C₁ * (n : ℝ) ^ ((17 : ℝ) / 12) := by
      calc (C * (n : ℝ) ^ (1 / 12 + ε)) * (n : ℝ) ^ ((17 : ℝ) / 12)
          = C * ((n : ℝ) ^ ((17 : ℝ) / 12) * (n : ℝ) ^ (1 / 12 + ε)) := by ring
        _ ≤ C₁ * (n : ℝ) ^ ((17 : ℝ) / 12) := h4
    exact le_of_mul_le_mul_right h5 hpos
  have hlt : C₁ < C * (n : ℝ) ^ (1 / 12 + ε) := by
    have := (div_lt_iff₀ hC).mp h2'
    linarith
  linarith

/-- `containsSubgraph147 F H` is Mathlib's `H ⊑ F`, an injective homomorphism from `H` to `F` (PROVED in Lean). -/
theorem erdos_problem_147.variants.containsSubgraph_iff {V U : Type*} (F : SimpleGraph V)
    (H : SimpleGraph U) : containsSubgraph147 F H ↔ H ⊑ F := by
  constructor
  · rintro ⟨f, hinj, hadj⟩
    exact ⟨⟨⟨f, fun {u v} h => hadj u v h⟩, hinj⟩⟩
  · rintro ⟨c⟩
    exact ⟨c, c.injective, fun u v h => c.toHom.map_adj h⟩

/--
`turanNumber147 H n` is Mathlib's `SimpleGraph.extremalNumber n H` (PROVED in Lean): the maximum number of
edges of an `H`-free graph on `n` vertices, whichever `n`-element type carries it.
-/
theorem erdos_problem_147.variants.turanNumber_eq_extremalNumber {U : Type*} (H : SimpleGraph U)
    (n : ℕ) : turanNumber147 H n = extremalNumber n H := by
  classical
  unfold turanNumber147
  apply le_antisymm
  · apply csSup_le'
    rintro m ⟨V, fv, F, dr, hc, hF, rfl⟩
    letI := fv
    letI := dr
    rw [extremalNumber_of_fintypeCard_eq hc]
    have hmem : F ∈ ({G : SimpleGraph V | H.Free G} : Finset (SimpleGraph V)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [Free, ← erdos_problem_147.variants.containsSubgraph_iff]
    convert Finset.le_sup (f := fun G : SimpleGraph V => G.edgeFinset.card) hmem
  · unfold extremalNumber
    apply Finset.sup_le
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    apply le_csSup
    · refine ⟨n.choose 2, ?_⟩
      rintro m ⟨V, fv, F, dr, hc, _, rfl⟩
      letI := fv
      letI := dr
      rw [← hc]
      exact card_edgeFinset_le_card_choose_two
    · refine ⟨Fin n, inferInstance, G, Classical.decRel _, ?_⟩
      refine ⟨by simp, ?_, ?_⟩
      · rwa [erdos_problem_147.variants.containsSubgraph_iff]
      · convert rfl
