-- [AI - Claude Sonnet 5.5]: Erdős Problem 150 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open SimpleGraph Real Filter

noncomputable section

/-!
# Erdős Problem #150: The number of minimal cuts of a graph

*Source:* [erdosproblems.com/150](https://www.erdosproblems.com/150) (banner **PROVED**: "This has been solved in the
affirmative."; captured 2026-02-20 as the page and as the tidied problem box, with identical content; the page shows
no edit date). [Er88]

A minimal cut of a graph is a minimal set of vertices whose removal disconnects the graph. Let $c(n)$ be the maximum
number of minimal cuts a graph on $n$ vertices can have.

Does $c(n)^{1/n}\to \alpha$ for some $\alpha <2$?

Remarks recorded on the page:
* Asked by Erdős and Nešetřil, who also ask whether $c(3m+2)=3^m$. Seymour observed that $c(3m+2)\geq 3^m$, as seen
  by the graph of $m$ independent paths of length $4$ joining two vertices.
* Solved by Bradač [Br24], who proved that $\alpha=\lim c(n)^{1/n}$ exists and
  $\alpha \leq 2^{H(1/3)}=1.8899\cdots$, where $H(\cdot)$ is the binary entropy function. Seymour's construction
  proves that $\alpha\geq 3^{1/3}=1.442\cdots$. Bradač conjectures that this lower bound is the true value of
  $\alpha$.

Tags: graph theory. OEIS: "Possible". 0 comments at capture.

**Status.** PROVED in the affirmative [Br24]. The mirror (`teorth/erdosproblems`) has `proved (Lean)` (2026-03-31), no
prize, formalised `yes`; upstream's `150.lean` (`df3f12d`) links a Lean proof (not examined here), so the `sorry` of
the main theorem stands for a proved theorem.

**Later developments (recorded by upstream's `150.lean`, not on the captured page). DEFERRED:** not checked against
the papers. Upstream says that $\alpha<2$ was first proved by [FKTV08], with $\alpha\le1.7087$, that the best known
bounds are $1.4457\le\alpha\le\frac{1+\sqrt5}2$ ([GaMa18] for the lower bound, [FoVi12] for the upper bound), and that
the lower bound answers the question $c(3m+2)=3^m$ in the negative. If the lower bound is correct, it also contradicts
the conjecture $\alpha=3^{1/3}$ of the page, since $1.4457>3^{1/3}=1.4422\cdots$. They are variants below.

**Encoding.**
* `IsVertexSeparator G S` says that removing `S` leaves a graph that is not preconnected, that is, at least two
  vertices that no path joins. The first pass wrote `¬ (G.induce Sᶜ).Connected`. Mathlib's `Connected` requires a
  nonempty vertex type, so that also held for `S = univ`, and the whole vertex set was counted as a minimal cut of
  every graph that has no vertex cut (the complete graphs), giving `numMinimalVertexCuts ⊤ = 1` instead of `0` and
  `c 1 = c 2 = 1` instead of `0`. `variants.separator_iff_firstPass` proves that the two readings differ by `S = univ`
  only. The change does not affect the limit, since for `n ≥ 3` the connected graphs that are not complete have a
  vertex cut, and the maximum is attained there. This is upstream's reading (`Preconnected`).
* "Minimal" is inclusion-minimal. An inclusion-minimal set whose removal disconnects the graph is a minimal separator
  in the usual sense (every component of the remainder is adjacent to every vertex of the set); the converse fails.
  **DEFERRED:** whether the bounds recorded as later developments are for this count.
* `c n` is the maximum over *connected* graphs on `Fin n`. A disconnected graph has only the empty set as a minimal
  cut, so for `n ≥ 3` this is the page's `c(n)`. `sSup` of the set is a maximum, since there are finitely many graphs.
* `variants.numMinimalVertexCuts_cycleGraph_five`, `numMinimalVertexCuts_path_five` and `numMinimalVertexCuts_top`
  prove in Lean that $C_5$ has 5 minimal cuts, the path with 5 vertices (the graph of the page's construction for
  $m=1$) has 3, and the complete graphs have none. So `c 5 ≥ 5` (`variants.c_five`) and the question $c(3m+2)=3^m$ has
  the answer *no*, already at $m=1$ (`variants.erdos_nesetril`).
* `erdos_problem_150.bradacBound` is $2^{H(1/3)}$ written as `exp (binEntropy (1/3))` (Mathlib's `binEntropy` uses the
  natural logarithm, and $2^{H(p)}=e^{h(p)}$ for $h$ the natural-logarithm entropy). `variants.bradacBound_eq` and
  `variants.bradacBound_bounds` prove that it is $3/2^{2/3}\in(1.8897,1.8899)$, and `variants.bradacBound_lt_two` that
  it is less than $2$. `variants.main_of_bradac` derives the main theorem from the two facts of [Br24], and
  `variants.lower_bound_of_seymour` derives $\alpha\ge3^{1/3}$ from Seymour's bound.

## References

* [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_. Discrete Math. (1988), 81–92.
* [Br24] Bradač, D., _On a question of Erdős and Nesetril about minimal cuts in a graph_. arXiv:2409.02974 (2024).
* [FKTV08] Fomin, F. V., Kratsch, D., Todinca, I. and Villanger, Y., _Exact algorithms for treewidth and minimum
  fill-in_. SIAM J. Comput. (2008), 1058–1079. (From upstream's docstring. **DEFERRED:** not on the captured page.)
* [FoVi12] Fomin, F. V. and Villanger, Y., _Treewidth computation and extremal combinatorics_. Combinatorica (2012),
  289–308. (From upstream's docstring. **DEFERRED.**)
* [GaMa18] Gaspers, S. and Mackenzie, S., _On the number of minimal separators in graphs_. J. Graph Theory (2018),
  653–659. (From upstream's docstring. **DEFERRED.**)

(Provenance: [Br24] is from the `/latex/150` fetch in the session logs and [Er88] from the `/latex/934`, `/latex/77`
and `/latex/151` fetches. **DEFERRED:** the page's own bibliography was seen only for [Br24].)
-/

/-- A set S of vertices is a vertex separator of G if the subgraph induced by
    the complement V \ S is disconnected, that is, not preconnected. (The empty graph and a one-vertex graph are
    preconnected, so S = V is not a separator. The first pass wrote `¬ ... .Connected`, which holds for the empty
    graph; see `variants.separator_iff_firstPass`.) -/
def IsVertexSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ¬(G.induce ((S : Set (Fin n))ᶜ)).Preconnected

/-- S is a minimal vertex cut of G if S is a vertex separator and no proper
    subset of S is also a vertex separator. -/
def IsMinimalVertexCut {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  IsVertexSeparator G S ∧
  ∀ T : Finset (Fin n), T ⊂ S → ¬IsVertexSeparator G T

/-- The number of minimal vertex cuts of G. -/
noncomputable def numMinimalVertexCuts {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  Set.ncard { S : Finset (Fin n) | IsMinimalVertexCut G S }

/-- c(n) is the maximum number of minimal vertex cuts over all connected simple
    graphs on n vertices. -/
noncomputable def c (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ G : SimpleGraph (Fin n), G.Connected ∧
    numMinimalVertexCuts G = k }

/--
Erdős Problem #150 [Er88] (asked by Erdős and Nešetřil) — PROVED [Br24]:
Let c(n) be the maximum number of minimal vertex cuts in a graph on n vertices.
Does c(n)^(1/n) → α for some α < 2?

Proved by Bradač [Br24]: the limit α = lim c(n)^(1/n) exists and
α ≤ 2^H(1/3) = 1.8899... < 2, where H(·) is the binary entropy function.
Seymour's construction gives c(3m+2) ≥ 3^m, so α ≥ 3^(1/3) ≈ 1.442.
Bradač conjectures that the true value is α = 3^(1/3).
-/
theorem erdos_problem_150 :
    ∃ α : ℝ, α < 2 ∧
      Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds α) :=
  sorry

/-- Being a vertex separator is decidable (used to evaluate the counts below by `decide`). -/
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Decidable (IsVertexSeparator G S) := by
  unfold IsVertexSeparator; infer_instance

/-- Being a minimal vertex cut is decidable. -/
instance {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) :
    Decidable (IsMinimalVertexCut G S) := by
  unfold IsMinimalVertexCut; infer_instance

/-- The number of minimal vertex cuts is the cardinality of a finset (PROVED in Lean). -/
theorem erdos_problem_150.numMinimalVertexCuts_eq_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    numMinimalVertexCuts G =
      (Finset.univ.filter (fun S : Finset (Fin n) => IsMinimalVertexCut G S)).card := by
  unfold numMinimalVertexCuts
  rw [← Set.ncard_coe_finset]
  congr 1
  ext S
  simp

/--
The whole vertex set is never a separator (PROVED in Lean), and the first pass's separators are v2's separators
together with the whole vertex set: the two readings of "removal disconnects the graph" differ at `S = univ` only,
where the remainder is empty.
-/
theorem erdos_problem_150.variants.separator_iff_firstPass {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    IsVertexSeparator G S ↔ ¬(G.induce ((S : Set (Fin n))ᶜ)).Connected ∧ S ≠ Finset.univ := by
  unfold IsVertexSeparator
  constructor
  · intro h
    refine ⟨fun hc => h hc.preconnected, ?_⟩
    rintro rfl
    exact h (by intro u; exact absurd u.2 (by simp))
  · rintro ⟨h1, h2⟩ h3
    apply h1
    have hne : Nonempty ↥((S : Set (Fin n))ᶜ) := by
      obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
        by_contra hcon
        push_neg at hcon
        exact h2 (Finset.eq_univ_iff_forall.mpr hcon)
      exact ⟨⟨x, by simpa using hx⟩⟩
    haveI := hne
    exact ⟨h3⟩

/-- The whole vertex set is not a separator (PROVED in Lean). -/
theorem erdos_problem_150.variants.univ_not_separator {n : ℕ} (G : SimpleGraph (Fin n)) :
    ¬ IsVertexSeparator G Finset.univ := by
  unfold IsVertexSeparator
  intro h
  apply h
  intro u
  exact absurd u.2 (by simp)

/-- A complete graph has no minimal cut (PROVED in Lean). The first pass counted one (the whole vertex set). -/
theorem erdos_problem_150.variants.numMinimalVertexCuts_top (n : ℕ) :
    numMinimalVertexCuts (⊤ : SimpleGraph (Fin n)) = 0 := by
  unfold numMinimalVertexCuts
  have : { S : Finset (Fin n) | IsMinimalVertexCut (⊤ : SimpleGraph (Fin n)) S } = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    apply h.1
    intro u v
    by_cases huv : u = v
    · subst huv; exact Reachable.refl u
    · exact Adj.reachable (by simp [huv])
  rw [this]; simp

/-- The five-cycle has five minimal cuts, the pairs of non-adjacent vertices (PROVED in Lean, by `decide`). -/
theorem erdos_problem_150.variants.numMinimalVertexCuts_cycleGraph_five :
    numMinimalVertexCuts (cycleGraph 5) = 5 := by
  rw [erdos_problem_150.numMinimalVertexCuts_eq_card]
  decide

/-- The path on five vertices (`0 - 1 - 2 - 3 - 4`): the page's graph of `m` independent paths of length `4` joining two
vertices, for `m = 1`. -/
def erdos_problem_150.pathFive : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel (fun a b : Fin 5 => a.val + 1 = b.val)

/-- Adjacency of the path on five vertices is decidable. -/
instance : DecidableRel erdos_problem_150.pathFive.Adj := fun a b => by
  unfold erdos_problem_150.pathFive; simp only [SimpleGraph.fromRel_adj]; infer_instance

/-- The path on five vertices has three minimal cuts, `3 ^ 1` as in Seymour's observation (PROVED in Lean). -/
theorem erdos_problem_150.variants.numMinimalVertexCuts_path_five :
    numMinimalVertexCuts erdos_problem_150.pathFive = 3 := by
  rw [erdos_problem_150.numMinimalVertexCuts_eq_card]
  decide

/-- `c 5 ≥ 5` (PROVED in Lean): the five-cycle is connected and has five minimal cuts. -/
theorem erdos_problem_150.variants.c_five : 5 ≤ c 5 := by
  have hbdd : BddAbove { k : ℕ | ∃ G : SimpleGraph (Fin 5), G.Connected ∧
      numMinimalVertexCuts G = k } := by
    refine ⟨2 ^ 5, ?_⟩
    rintro k ⟨G, -, rfl⟩
    unfold numMinimalVertexCuts
    calc Set.ncard { S : Finset (Fin 5) | IsMinimalVertexCut G S }
        ≤ Nat.card (Finset (Fin 5)) := Set.ncard_le_card _
      _ = 2 ^ 5 := by simp
  have hc5 : (cycleGraph 5).Connected := by decide
  have := le_csSup hbdd ⟨cycleGraph 5, hc5, rfl⟩
  rw [erdos_problem_150.variants.numMinimalVertexCuts_cycleGraph_five] at this
  exact this

/--
Erdős and Nešetřil's question whether `c(3m+2) = 3^m` has the answer *no* (PROVED in Lean): `c 5 ≥ 5 > 3 = 3 ^ 1`.
Upstream attributes the negative answer to the lower bound `1.4457 ≤ α` of [GaMa18], which is not needed at `m = 1`.
**DEFERRED:** whether [Er88] means the same notion of minimal cut (the page's own definition is used here).
-/
theorem erdos_problem_150.variants.erdos_nesetril : ¬ ∀ m : ℕ, c (3 * m + 2) = 3 ^ m := by
  intro h
  have h1 := h 1
  have h5 := erdos_problem_150.variants.c_five
  norm_num at h1
  omega

/-- The constant `2 ^ H(1/3)` of [Br24] with `H` the binary entropy, as `exp` of Mathlib's natural-logarithm entropy. -/
def erdos_problem_150.bradacBound : ℝ := Real.exp (Real.binEntropy (1 / 3))

/-- `2 ^ H(1/3) < 2` (PROVED in Lean), which is why [Br24] answers the question. -/
theorem erdos_problem_150.variants.bradacBound_lt_two : erdos_problem_150.bradacBound < 2 := by
  have h : Real.binEntropy (1 / 3) < Real.log 2 := by
    rw [Real.binEntropy_lt_log_two]
    norm_num
  calc erdos_problem_150.bradacBound = Real.exp (Real.binEntropy (1 / 3)) := rfl
    _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr h
    _ = 2 := Real.exp_log (by norm_num)

/-- `2 ^ H(1/3) = 3 / 2 ^ (2/3)` (PROVED in Lean). -/
theorem erdos_problem_150.variants.bradacBound_eq :
    erdos_problem_150.bradacBound = 3 / (2 : ℝ) ^ ((2 : ℝ) / 3) := by
  unfold erdos_problem_150.bradacBound Real.binEntropy
  have h1 : ((1 : ℝ) / 3)⁻¹ = 3 := by norm_num
  have h2 : (1 - (1 : ℝ) / 3)⁻¹ = 3 / 2 := by norm_num
  rw [h1, h2]
  have h3 : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  rw [h3]
  have h4 : (1 / 3 : ℝ) * Real.log 3 + (1 - 1 / 3) * (Real.log 3 - Real.log 2)
      = Real.log 3 - (2 / 3) * Real.log 2 := by ring
  rw [h4, Real.exp_sub, Real.exp_log (by norm_num)]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

/-- `(2 ^ (2/3)) ^ 3 = 4` (PROVED in Lean). -/
theorem erdos_problem_150.rpow_two_thirds_cube : ((2 : ℝ) ^ ((2 : ℝ) / 3)) ^ 3 = 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- `1.8897 < 2 ^ H(1/3) < 1.8899` (PROVED in Lean), the page's `1.8899⋯`. -/
theorem erdos_problem_150.variants.bradacBound_bounds :
    (1.8897 : ℝ) < erdos_problem_150.bradacBound ∧ erdos_problem_150.bradacBound < 1.8899 := by
  have hx : (0 : ℝ) < (2 : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  have h3 := erdos_problem_150.rpow_two_thirds_cube
  rw [erdos_problem_150.variants.bradacBound_eq]
  generalize (2 : ℝ) ^ ((2 : ℝ) / 3) = x at hx h3 ⊢
  have hlo : (1.5874 : ℝ) < x := by
    by_contra h
    push_neg at h
    have := pow_le_pow_left₀ hx.le h 3
    norm_num at this
    linarith
  have hhi : x < (1.5875 : ℝ) := by
    by_contra h
    push_neg at h
    have := pow_le_pow_left₀ (by norm_num) h 3
    norm_num at this
    linarith
  constructor
  · rw [lt_div_iff₀ hx]; nlinarith
  · rw [div_lt_iff₀ hx]; nlinarith

/--
[Br24] answers the question (PROVED in Lean from the two facts of [Br24]): if the limit exists and is at most
`2 ^ H(1/3)`, then there is `α < 2` with `c(n)^(1/n) → α`.
-/
theorem erdos_problem_150.variants.main_of_bradac
    (hlim : ∃ α : ℝ, Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α))
    (hbd : ∀ α : ℝ, Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α) →
      α ≤ erdos_problem_150.bradacBound) :
    ∃ α : ℝ, α < 2 ∧ Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α) := by
  obtain ⟨α, hα⟩ := hlim
  exact ⟨α, lt_of_le_of_lt (hbd α hα) erdos_problem_150.variants.bradacBound_lt_two, hα⟩

/-- A bound `3 ^ m ≤ a (3 * m + 2)` gives `3 ^ (1/3) ≤ α` for any limit `α` of `a n ^ (1/n)` (PROVED in Lean). -/
theorem erdos_problem_150.lower_bound_of_subseq (a : ℕ → ℕ)
    (hs : ∀ m : ℕ, 3 ^ m ≤ a (3 * m + 2)) (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ α := by
  have hsub : Tendsto (fun m : ℕ => 3 * m + 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun x hx => by omega⟩
  have h1 : Tendsto (fun m : ℕ => (a (3 * m + 2) : ℝ) ^ ((1 : ℝ) / ((3 * m + 2 : ℕ) : ℝ)))
      atTop (nhds α) := hα.comp hsub
  have h2 : Tendsto (fun m : ℕ => (m : ℝ) / (3 * m + 2)) atTop (nhds (1 / 3)) := by
    have h := (tendsto_natCast_div_add_atTop (2 / 3 : ℝ)).const_mul (1 / 3 : ℝ)
    have h' : Tendsto (fun m : ℕ => (1 / 3 : ℝ) * ((m : ℝ) / (m + 2 / 3))) atTop
        (nhds (1 / 3 * 1)) := h
    rw [mul_one] at h'
    refine h'.congr (fun m => ?_)
    have : (m : ℝ) + 2 / 3 ≠ 0 := by positivity
    field_simp
  have h3 : Tendsto (fun m : ℕ => (3 : ℝ) ^ ((m : ℝ) / (3 * m + 2))) atTop
      (nhds ((3 : ℝ) ^ ((1 : ℝ) / 3))) :=
    ((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).tendsto _).comp h2
  refine le_of_tendsto_of_tendsto' h3 h1 (fun m => ?_)
  have hpos : (0 : ℝ) < ((3 * m + 2 : ℕ) : ℝ) := by positivity
  have hcast : (((3 * m + 2 : ℕ) : ℝ)) = 3 * (m : ℝ) + 2 := by push_cast; ring
  have e1 : (3 : ℝ) ^ ((m : ℝ) / (3 * m + 2)) =
      ((3 : ℝ) ^ m) ^ ((1 : ℝ) / ((3 * m + 2 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hcast]
    congr 1
    field_simp
  rw [e1]
  apply Real.rpow_le_rpow (by positivity)
  · exact_mod_cast hs m
  · positivity

/-- Seymour's observation on the page (PROVED, not checked here): the graph of `m` independent paths of length `4`
joining two vertices has at least `3 ^ m` minimal cuts, one vertex from each path, so `c (3m+2) ≥ 3 ^ m`. -/
theorem erdos_problem_150.variants.seymour (m : ℕ) : 3 ^ m ≤ c (3 * m + 2) :=
  sorry

/-- Seymour's construction gives `α ≥ 3 ^ (1/3) = 1.442⋯` (the page; PROVED in Lean from `variants.seymour`). -/
theorem erdos_problem_150.variants.lower_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    (3 : ℝ) ^ ((1 : ℝ) / 3) ≤ α :=
  erdos_problem_150.lower_bound_of_subseq c erdos_problem_150.variants.seymour α hα

/-- Bradač [Br24] (PROVED, not checked here): the limit `α = lim c(n)^(1/n)` exists. -/
theorem erdos_problem_150.variants.limit_exists :
    ∃ α : ℝ, Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α) :=
  sorry

/-- Bradač [Br24] (PROVED, not checked here): `α ≤ 2 ^ H(1/3) = 1.8899⋯`. -/
theorem erdos_problem_150.variants.bradac_upper_bound (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    α ≤ erdos_problem_150.bradacBound :=
  sorry

/-- Fomin, Kratsch, Todinca and Villanger [FKTV08], as recorded by upstream (not on the captured page. **DEFERRED:**
not checked here): `α ≤ 1.7087`. -/
theorem erdos_problem_150.variants.fomin_kratsch_todinca_villanger (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    α ≤ 1.7087 :=
  sorry

/-- Fomin and Villanger [FoVi12], as recorded by upstream (not on the captured page. **DEFERRED:** not checked
here): `α ≤ (1 + √5) / 2 ≈ 1.618`. -/
theorem erdos_problem_150.variants.fomin_villanger (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    α ≤ (1 + Real.sqrt 5) / 2 :=
  sorry

/-- Gaspers and Mackenzie [GaMa18], as recorded by upstream (not on the captured page. **DEFERRED:** not checked
here): `1.4457 ≤ α`, which would contradict the conjecture `α = 3 ^ (1/3)` of the page. -/
theorem erdos_problem_150.variants.gaspers_mackenzie (α : ℝ)
    (hα : Tendsto (fun n : ℕ => (c n : ℝ) ^ ((1 : ℝ) / (n : ℝ))) atTop (nhds α)) :
    1.4457 ≤ α :=
  sorry

end
