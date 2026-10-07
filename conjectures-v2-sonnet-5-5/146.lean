-- [AI - Claude Sonnet 5.5]: Erdős Problem 146 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open SimpleGraph
open Filter

/-!
# Erdős Problem #146: The Erdős–Simonovits degeneracy conjecture (DISPROVED)

*Source:* [erdosproblems.com/146](https://www.erdosproblems.com/146) (banner **OPEN**, prize **\$500** at
capture: "This is open, and cannot be resolved with a finite computation."; page last edited 18 January 2026;
captured 2026-02-20 as the page and as the tidied problem box, with identical content; **disproved
since**, see below). [ErSi84] [Er91] [Er93] [Er97c]

If $H$ is bipartite and is $r$-degenerate, that is, every induced subgraph of $H$ has minimum degree
$\leq r$, then $\mathrm{ex}(n;H) \ll n^{2-1/r}$.

Remarks recorded on the page:
* Conjectured by Erdős and Simonovits [ErSi84]. Open even for $r=2$. Alon, Krivelevich and Sudakov [AKS03]
  have proved $\mathrm{ex}(n;H) \ll n^{2-1/4r}$. They also prove the full Erdős–Simonovits conjectured bound
  if $H$ is bipartite and the maximum degree in one side of the bipartition is $r$.
* See also [113] and [147].
* This problem is #43 in Extremal Graph Theory in the graphs problem collection.

Tags: graph theory, turán number. 2 comments at capture (not captured).

**Status after capture.** The site owner's mirror (`teorth/erdosproblems`) records `open (Lean)` from commit
`be86208` (2026-08-02, "record Lean refutations of problems 146 and 180"), with a formal-status link to
`openai/ten-proofs` and the note "counterexample; refutes the degeneracy conjecture", and `disproved (Lean)`
from commit `7b7132c` (2026-08-31), with prize \$500. Upstream `146.lean` has
`erdos_146 : answer(False) ↔ …`, category `research solved`, and `variants.two_degenerate_counterexample` with
the same formal-proof link. The counterexample [OpenAI26] is a connected bipartite $2$-degenerate $H$ with
$\mathrm{ex}(n;H)\ge c\,n^{3/2+\varepsilon}$ for all large $n$, which exceeds the conjectured $n^{2-1/2}$.

**What the first pass did, and what this file does.** The first pass asserts the conjecture, the asked
direction while the problem was open. The conjecture is now recorded as false, so v2 asserts its negation
(`erdos_problem_146`), with the first pass's proposition byte-identical inside `¬`, and keeps all three of the
first pass's definitions. The refutation is not proved here: `variants.two_degenerate_counterexample` states
the counterexample and keeps its `sorry`, and `variants.refutation_of_counterexample` proves in Lean that the
counterexample implies the negation.

**Encoding.**
* "Bipartite" is `Nonempty (H.Coloring (Fin 2))`. "$r$-degenerate" is `IsRDegenerateGraph H r`: every
  non-empty finite vertex set has a vertex with at most `r` neighbours inside it, which for a finite graph is
  "every induced subgraph has minimum degree $\le r$". "$\ll$" is read as `∃ C > 0, ∀ n ≥ 1, … ≤ C * n ^ …`, for
  fixed `r` and `H`. The first finitely many `n` are absorbed in `C`.
* `turanNumber146 H n` is the maximum number of edges of a graph on `n` vertices with no injective
  homomorphic copy of `H`. `variants.containsSubgraph_iff` shows that `containsSubgraph146 F H` is Mathlib's
  `H ⊑ F`, and `variants.turanNumber_eq_extremalNumber` shows that `turanNumber146 H n` equals Mathlib's
  `SimpleGraph.extremalNumber n H`. `variants.mantel_four` checks `ex(4; K₃) = 4`, the value of Mantel's
  theorem.
* If every `n`-vertex graph contains `H` (for example `H` edgeless with at most `n` vertices) the family is
  empty and both definitions give `0`. This is a convention, and it cannot affect the conjecture's bound.
* The theorem quantifies over `U : Type*`. `variants.two_degenerate_counterexample` is stated in the same
  universe, which is no restriction because a finite graph can be moved between universes by `ULift`.
* `variants.aks_degenerate` and `variants.aks_one_side` are the two results of [AKS03] recorded on the page.
  The page prints the first exponent as `2-1/4r`, read here as $2-\frac1{4r}$.

## References

* [ErSi84] Erdős, P. and Simonovits, M., _Cube-supersaturated graphs and related problems_. In: Progress in
  graph theory (Waterloo, Ont., 1982) (1984), 203–218.
* [AKS03] Alon, N., Krivelevich, M. and Sudakov, B., _Turán numbers of bipartite graphs and related
  Ramsey-type questions_. Combin. Probab. Comput. (2003), 477–494.
* [Er91] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number theory_. In:
  Graph theory, combinatorics, and applications, Vol. 1 (Kalamazoo, MI, 1988) (1991).
* [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_. Quaestiones Math.
  (1993), 333–350.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. In: The mathematics of Paul Erdős, I
  (1997), 47–67.
* [OpenAI26] OpenAI, _Ten advances in mathematics and theoretical computer science_ (2026). The formal
  proof is linked from the mirror and upstream (`openai/ten-proofs`, `CompactnessAndDegeneracy.lean`).
  **DEFERRED:** the paper and the proof were not read, and the exact form of the counterexample (connectedness,
  the exponent $3/2+\varepsilon$) is upstream's.
* [113], [147] The page's cross-references to Problems 113 and 147.

(Provenance: [ErSi84] and [AKS03] are from the `/latex/146` fetch in the session logs. [Er91], [Er93] and
[Er97c] are from the bibliographies of the `/latex` pages of other problems. [OpenAI26] is from upstream
`146.lean`.)
-/

/-- An injective graph homomorphism from H to F; witnesses that F contains a
    subgraph isomorphic to H. -/
def containsSubgraph146 {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber146 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph146 F H ∧ F.edgeFinset.card = m}

/-- A graph G is r-degenerate if every non-empty finite set of vertices contains
    a vertex with at most r neighbors within that set. Equivalently, every induced
    subgraph of G has minimum degree at most r. -/
def IsRDegenerateGraph {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ r

/--
Erdős-Simonovits Conjecture (Problem #146) [ErSi84] — DISPROVED [OpenAI26] (not checked here):
If H is a bipartite graph that is r-degenerate (i.e., every induced subgraph of H
has minimum degree at most r), then

  ex(n; H) ≪ n^{2 - 1/r}

That is, there exists a constant C > 0 such that ex(n; H) ≤ C · n^{2 - 1/r} for all n ≥ 1.

The page was OPEN at capture ("open even for r = 2"; Alon, Krivelevich and Sudakov [AKS03] proved the
weaker bound ex(n; H) ≪ n^{2 - 1/(4r)}). The conjecture has since been refuted, already for r = 2, so this
file states the negation of the first pass's proposition.
-/
theorem erdos_problem_146 :
    ¬ (∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      IsRDegenerateGraph H r →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber146 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ))) :=
  sorry

/--
The counterexample of [OpenAI26] (PROVED there in Lean, not checked here): a connected bipartite
`2`-degenerate graph `H` with `ex(n; H) ≥ c * n ^ (3 / 2 + ε)` for all large `n`, for some `c, ε > 0`. This is
upstream's form. It is stated for a type in an arbitrary universe, as the main theorem is.
-/
theorem erdos_problem_146.variants.two_degenerate_counterexample.{u} :
    ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
      H.Connected ∧ Nonempty (H.Coloring (Fin 2)) ∧ IsRDegenerateGraph H 2 ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤ (turanNumber146 H n : ℝ) :=
  sorry

/--
The counterexample refutes the conjecture (PROVED in Lean): for `r = 2` the conjectured bound is
`C * n ^ (3 / 2)`, and `n ^ ε → ∞` shows that `c * n ^ (3 / 2 + ε)` exceeds it for large `n`.
-/
theorem erdos_problem_146.variants.refutation_of_counterexample.{u}
    (h : ∃ (U : Type u) (_ : Fintype U) (H : SimpleGraph U),
      H.Connected ∧ Nonempty (H.Coloring (Fin 2)) ∧ IsRDegenerateGraph H 2 ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) ≤ (turanNumber146 H n : ℝ)) :
    ¬ (∀ (r : ℕ), 1 ≤ r →
      ∀ (U : Type u) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
        Nonempty (H.Coloring (Fin 2)) →
        IsRDegenerateGraph H r →
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
          (turanNumber146 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ))) := by
  intro hconj
  obtain ⟨U, fU, H, -, hbip, hdeg, c, ε, hc, hε, hev⟩ := h
  obtain ⟨C, hC, hbound⟩ := @hconj 2 (by norm_num) U H fU (Classical.decRel _) hbip hdeg
  have h2 : (2 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 3 / 2 := by norm_num
  rw [h2] at hbound
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C / c < (n : ℝ) ^ ε := htend.eventually_gt_atTop (C / c)
  obtain ⟨n, h1, h2', h3⟩ := (hev.and (hlarge.and (eventually_ge_atTop 1))).exists
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h3
  have hb := hbound n h3
  rw [Real.rpow_add hnpos] at h1
  have hpos : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hnpos _
  have hle : c * (n : ℝ) ^ ε ≤ C := by
    have h4 : c * ((n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ε) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) :=
      le_trans h1 hb
    have h5 : (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      calc (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2)
          = c * ((n : ℝ) ^ ((3 : ℝ) / 2) * (n : ℝ) ^ ε) := by ring
        _ ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := h4
    exact le_of_mul_le_mul_right h5 hpos
  have hlt : C < c * (n : ℝ) ^ ε := by
    have := (div_lt_iff₀ hc).mp h2'
    linarith
  linarith

/--
[AKS03] (PROVED, not checked here): for bipartite `r`-degenerate `H`, `ex(n; H) ≪ n ^ (2 - 1 / (4 * r))`.
The page prints the exponent as `2-1/4r`.
-/
theorem erdos_problem_146.variants.aks_degenerate :
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      IsRDegenerateGraph H r →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber146 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (4 * (r : ℝ))) :=
  sorry

/--
[AKS03] (PROVED, not checked here): the full conjectured bound `ex(n; H) ≪ n ^ (2 - 1 / r)` holds if `H` has
a proper `2`-colouring in which every vertex of colour `0` has at most `r` neighbours.
-/
theorem erdos_problem_146.variants.aks_one_side :
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj] (c : H.Coloring (Fin 2)),
      (∀ v, c v = 0 → (H.neighborSet v).ncard ≤ r) →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber146 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) :=
  sorry

/-- `containsSubgraph146 F H` is Mathlib's `H ⊑ F`, an injective homomorphism from `H` to `F` (PROVED in Lean). -/
theorem erdos_problem_146.variants.containsSubgraph_iff {V U : Type*} (F : SimpleGraph V)
    (H : SimpleGraph U) : containsSubgraph146 F H ↔ H ⊑ F := by
  constructor
  · rintro ⟨f, hinj, hadj⟩
    exact ⟨⟨⟨f, fun {u v} h => hadj u v h⟩, hinj⟩⟩
  · rintro ⟨c⟩
    exact ⟨c, c.injective, fun u v h => c.toHom.map_adj h⟩

/--
`turanNumber146 H n` is Mathlib's `SimpleGraph.extremalNumber n H` (PROVED in Lean): the maximum number of
edges of an `H`-free graph on `n` vertices, whichever `n`-element type carries it.
-/
theorem erdos_problem_146.variants.turanNumber_eq_extremalNumber {U : Type*} (H : SimpleGraph U)
    (n : ℕ) : turanNumber146 H n = extremalNumber n H := by
  classical
  unfold turanNumber146
  apply le_antisymm
  · apply csSup_le'
    rintro m ⟨V, fv, F, dr, hc, hF, rfl⟩
    letI := fv
    letI := dr
    rw [extremalNumber_of_fintypeCard_eq hc]
    have hmem : F ∈ ({G : SimpleGraph V | H.Free G} : Finset (SimpleGraph V)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [Free, ← erdos_problem_146.variants.containsSubgraph_iff]
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
      · rwa [erdos_problem_146.variants.containsSubgraph_iff]
      · convert rfl

/--
Mantel's value `ex(4; K₃) = 4` for the first pass's Turán number (PROVED in Lean), through the bridge to
Mathlib's `extremalNumber` and its Turán graph. It checks the definition against a classical value.
-/
theorem erdos_problem_146.variants.mantel_four : turanNumber146 (⊤ : SimpleGraph (Fin 3)) 4 = 4 := by
  rw [erdos_problem_146.variants.turanNumber_eq_extremalNumber, extremalNumber_top]
  decide +kernel
