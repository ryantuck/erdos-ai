-- [AI - Claude Sonnet 5.5]: Erdős Problem 134 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Basic

open Classical SimpleGraph Filter Real

noncomputable section

/-!
# Erdős Problem #134: Making a Sparse Triangle-Free Graph Have Diameter 2

*Source:* [erdosproblems.com/134](https://www.erdosproblems.com/134) (banner **PROVED (LEAN)**:
"This has been solved in the affirmative and the proof verified in Lean."; captured 2026-02-20 as
the tidied problem box). [Er97b]

Let $\epsilon,\delta>0$ and $n$ be sufficiently large in terms of $\epsilon$ and $\delta$. Let $G$
be a triangle-free graph on $n$ vertices with maximum degree $<n^{1/2-\epsilon}$.

Can $G$ be made into a triangle-free graph with diameter $2$ by adding at most $\delta n^2$
edges?

Remarks recorded on the page:
* Asked by Erdős and Gyárfás, who proved that this is the case when $G$ has maximum degree
  $\ll \log n/\log\log n$. A construction of Simonovits shows that this conjecture is false if we
  just have maximum degree $\leq Cn^{1/2}$, for some large enough $C$.
* In this note Alon solves this problem in a strong form, in particular proving that a
  triangle-free graph on $n$ vertices with maximum degree $<n^{1/2-\epsilon}$ can be made into a
  triangle-free graph with diameter $2$ by adding at most $O(n^{2-\epsilon})$ edges.
* See also [618].

Tags: graph theory. 1 comment at capture (not captured).

**Status.** PROVED (LEAN). The mirror (`teorth/erdosproblems`) has `proved (Lean)` (2026-02-07).
Upstream `erdos_134` is `answer(True) ↔ …`, category `research solved`, with a link to a Lean proof
in an external repository (`plby/lean-proofs`) that has not been checked here. The first pass
asserts the asked ("yes") direction, which is the proved one.

**Encoding.**
* `G ≤ H` on `Fin n` says that $H$ has the same vertices as $G$ and contains all of its edges, so
  $H$ is obtained by adding edges.
* `H.CliqueFree 3` is "triangle-free", and `HasDiameterAtMostTwo H` says that distinct vertices are
  adjacent or have a common neighbour. For $n\ge3$ a triangle-free graph of diameter at most $2$ has
  diameter exactly $2$, since the only triangle-free complete graphs are $K_1$ and $K_2$.
* The number of added edges is `|E(H)| − |E(G)|`, taken in ℝ, so there is no truncated natural
  subtraction. Since `G ≤ H` it is the number of edges of `H` that are not in `G`.
* `G.degree` and `edgeFinset` use the classical decidability instances from `open Classical`. The
  statement does not depend on the choice of instance.
* For $\epsilon\ge\tfrac12$ the bound $n^{1/2-\epsilon}$ is at most $1$, so $G$ has no edges and the
  statement is trivial.
* Alon's strong form implies the first statement: `variants.main_of_alon` proves it in Lean.
* The first pass cited a key `[Al94]` for Alon's result. That key is not on the page and is dropped.
  The page cites a note by Alon by a link only, the same note as on Problem 133.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* Alon's note, cited on the page by a link only
  (`https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf`). **DEFERRED:** no title or
  journal data was recovered, and the file name suggests January 2019.
* [618] The page's cross-reference.

(Provenance: [Er97b] is from upstream `134.lean`, which agrees with the bibliographies of the
`/latex` pages of other problems. The link is from the `/latex/134` fetch in the session logs.)
-/

/-- A graph has diameter at most 2 if every pair of distinct vertices is
    either adjacent or shares a common neighbor. -/
def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/--
Erdős Problem #134 [Er97b] — PROVED (LEAN) per the page, and proved by Alon in a strong form:

For every ε, δ > 0 and all sufficiently large n, every triangle-free graph on
n vertices with maximum degree < n^(1/2 - ε) can be extended to a triangle-free
graph with diameter ≤ 2 by adding at most δn² edges.
-/
theorem erdos_problem_134 :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ δ * (n : ℝ) ^ 2 :=
  sorry

/--
Alon's strong form (PROVED, not checked here):

For every ε > 0 there exists C > 0 such that for all sufficiently large n,
every triangle-free graph on n vertices with maximum degree < n^(1/2 - ε)
can be extended to a triangle-free graph with diameter ≤ 2 by adding at
most C · n^(2 - ε) edges.
-/
theorem erdos_problem_134.variants.alon :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (2 - ε) :=
  sorry

/--
The first statement follows from Alon's strong form (PROVED in Lean): for large $n$,
$C n^{2-\varepsilon} = C n^{-\varepsilon}\, n^2 \le \delta n^2$.
-/
theorem erdos_problem_134.variants.main_of_alon
    (halon : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (2 - ε)) :
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
  intro ε δ hε hδ
  obtain ⟨C, hC, hev⟩ := halon ε hε
  have h0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ε)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-ε) < δ / C :=
    h0.eventually (gt_mem_nhds (div_pos hδ hC))
  filter_upwards [hev, h1, eventually_gt_atTop 0] with n hn hlt hn0 G hG hdeg
  obtain ⟨H, hGH, hH, hD, hcard⟩ := hn G hG hdeg
  refine ⟨H, hGH, hH, hD, le_trans hcard ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have e : (n : ℝ) ^ (2 - ε) = (n : ℝ) ^ 2 * (n : ℝ) ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add hnpos]
    simp
  rw [e]
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have : C * (n : ℝ) ^ (-ε) < δ := by
    rw [lt_div_iff₀ hC] at hlt
    linarith
  nlinarith

/--
Simonovits's construction, as the page words it (PROVED, not checked here): the statement fails if
the maximum degree is only bounded by $C n^{1/2}$ for some large enough constant $C$. Formally,
there is a $C>0$ for which it is not true that, for every $\delta>0$ and all large $n$, every
triangle-free graph on $n$ vertices with maximum degree at most $C n^{1/2}$ can be extended to a
triangle-free graph of diameter at most $2$ by adding at most $\delta n^2$ edges.
-/
theorem erdos_problem_134.variants.simonovits :
    ∃ C : ℝ, 0 < C ∧ ¬ (∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ G : SimpleGraph (Fin n),
        G.CliqueFree 3 →
        (∀ v : Fin n, (G.degree v : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2)) →
        ∃ H : SimpleGraph (Fin n),
          G ≤ H ∧ H.CliqueFree 3 ∧ HasDiameterAtMostTwo H ∧
          (H.edgeFinset.card : ℝ) - (G.edgeFinset.card : ℝ) ≤ δ * (n : ℝ) ^ 2) :=
  sorry

end
