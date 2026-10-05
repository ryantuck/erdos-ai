-- [AI - Claude Sonnet 5.5]: Erdős Problem 133 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Filter

/-!
# Erdős Problem #133: Triangle-Free Graphs of Diameter 2 with Small Maximum Degree

*Source:* [erdosproblems.com/133](https://www.erdosproblems.com/133) (banner **DISPROVED**: "This
has been solved in the negative."; captured 2026-02-20 as the tidied problem box). [Er97b]

Let $f(n)$ be minimal such that every triangle-free graph $G$ with $n$ vertices and diameter $2$
contains a vertex with degree $\geq f(n)$.

What is the order of growth of $f(n)$? Does $f(n)/\sqrt{n}\to \infty$?

Remarks recorded on the page:
* Asked by Erdős and Pach. The lower bound $f(n)\geq (1-o(1))\sqrt{n}$ follows from the fact that
  a graph with maximum degree $d$ and diameter $2$ has at most $1+d+d(d-1)=d^2+1$ many vertices.
* Simonovits observed that the subsets of $[3m-1]$ of size $m$, two sets joined by edge if and
  only if they are disjoint, forms a triangle-free graph of diameter $2$ which is regular of
  degree $\binom{2m-1}{m}$. This construction proves that
  $f(n) \leq n^{(1+o(1))\frac{2}{3H(1/3)}}=n^{0.7182\cdots}$, where $H(x)$ is the binary entropy
  function. In [Er97b] Erdős encouraged the reader to try and find a better construction.
* In this note Alon provides a simple construction that proves $f(n) \ll \sqrt{n\log n}$: take a
  triangle-free graph with independence number $\ll \sqrt{n\log n}$ (the existence of which is the
  lower bound in [165]) and add edges until it has diameter $2$; the neighbourhood of any set is an
  independent set and hence the maximum degree is still $\ll \sqrt{n\log n}$.
* Hanson and Seyffarth [HaSe84] proved that $f(n)\leq (\sqrt{2}+o(1))\sqrt{n}$ using a Cayley
  graph on $\mathbb{Z}/n\mathbb{Z}$, with the generating set given by some symmetric complete
  sum-free set of size $\sim \sqrt{n}$. An alternative construction of such a complete sum-free
  set was given by Haviv and Levy [HaLe18].
* Füredi and Seress [FuSe94] proved that $f(n)\leq (\frac{2}{\sqrt{3}}+o(1))\sqrt{n}$.
* The precise asymptotics of $f(n)$ are unknown; Alon believes that the truth is
  $f(n)\sim \sqrt{n}$.

Tags: graph theory. OEIS: "Possible". 0 comments at capture.

**Status.** DISPROVED: the explicit question "does $f(n)/\sqrt n\to\infty$?" is answered no. The
mirror (`teorth/erdosproblems`) has `disproved` (2025-08-31). Upstream `erdos_133` is
`answer(False) ↔ …`, category `research solved`, with a link to a Lean proof in an external
repository that has not been checked here. The main theorem asserts the negation, the corpus
convention for a refuted statement. The order of growth is still open between $\sqrt n$ and
$(2/\sqrt3)\sqrt n$, and Alon's conjecture $f(n)\sim\sqrt n$ is recorded as `variants.alon_conjecture`.

**What the first pass got wrong, and what this file does.** The first pass defined `erdos133_f n`
as the `sInf` of the set of `k` such that every such graph has a vertex of degree at least `k`.
That set is closed downwards and contains $0$, so its `sInf` is $0$ for every $n$.
`variants.first_pass_f_eq_zero` proves it. Hence the first pass's Moore lower bound and its
statement of Alon's conjecture were false, and its upper bounds were true for a vacuous reason.
v2 takes the `sSup` of the same set, which is the largest `k` that every such graph reaches, that
is, the least possible maximum degree. `variants.f_two` checks that it is positive: $f(2)=1$.

**Encoding.**
* `HasDiameterAtMostTwo G` says that any two distinct vertices are adjacent or have a common
  neighbour, so $G$ is connected. The page says "diameter $2$". For $n\ge3$ a triangle-free graph
  of diameter at most $2$ has diameter exactly $2$, since the only triangle-free complete graphs are
  $K_1$ and $K_2$. For $n=2$ the family is $\{K_2\}$ and gives $f(2)=1$, which an exact diameter of
  $2$ would make empty. That changes nothing asymptotically.
* `erdos133_f n` is the `sSup` of a set that is empty for $n=0$ and bounded for $n\ge1$, because
  the family of such graphs on $n$ vertices is nonempty ($K_1$, $K_2$, a star) and any `k` in the set
  is at most the maximum degree of a member. So it is the true minimum of the maximum degree for
  $n\ge1$, and $0$ for $n=0$. Exhaustive search gives $f(2),\dots,f(8)=1,2,2,2,3,3,3$.
* The `[DecidableRel G.Adj]` binder inside the set makes `G.degree` available. The set quantifies
  over every graph and every decidability instance, which gives the same condition.
* "$f(n)/\sqrt n\to\infty$" is `Tendsto (fun n => f n / √n) atTop atTop` in $\mathbb R$.
* **A numerical slip on the page.** For Simonovits's construction the exponent is
  $2/(3H(1/3))=0.7260\ldots$, not $0.7182\ldots$: with $n=\binom{3m-1}{m}$ and degree
  $\binom{2m-1}{m}$, the ratio $\ln\deg/\ln n$ is $0.72598$ at $m=5000$ and tends to $0.725982$.
  The bound is not formalized.
* The first pass cited `[ErPa90]` for the Moore bound. That key is not on the page and is dropped.

## References

* [Er97b] Erdős, P., _Some old and new problems in various branches of combinatorics_. Discrete
  Math. (1997), 227–231.
* [HaSe84] Hanson, D. and Seyffarth, K., _k-saturated graphs of prescribed maximum degree_. Congr.
  Numer. (1984), 169–182.
* [FuSe94] Füredi, Z. and Seress, Á., _Maximal triangle-free graphs with restrictions on the
  degrees_. J. Graph Theory (1994), 11–24.
* [HaLe18] Haviv, I. and Levy, D., _Symmetric complete sum-free sets in cyclic groups_. Israel J.
  Math. (2018), 931–956.
* Alon's note, cited on the page by a link only
  (`https://web.math.princeton.edu/~nalon/PDFS/remark1901.pdf`). **DEFERRED:** no title or
  journal data was recovered, and the file name suggests January 2019.
* [165] The page's cross-reference for the independence-number bound.

(Provenance: the four entries are from the `/latex/133` fetch in the session logs.)
-/

/-- A graph $G$ contains a triangle if there are three mutually adjacent vertices. -/
def HasTriangle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ a b c : V, G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- A graph has diameter at most 2 if every pair of distinct vertices is
    either directly adjacent or has a common neighbor. -/
def HasDiameterAtMostTwo {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → G.Adj u v ∨ ∃ w : V, G.Adj u w ∧ G.Adj w v

/-- $\mathrm{erdos133\_f}(n)$ is the largest $k$ such that every triangle-free
    graph on $n$ vertices with diameter at most $2$ contains a vertex of degree
    at least $k$.  Equivalently, it is the minimum maximum-degree over all such
    graphs.  The set of such $k$ is empty for $n = 0$, where the supremum is $0$. -/
noncomputable def erdos133_f (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬HasTriangle G → HasDiameterAtMostTwo G →
    ∃ v : Fin n, k ≤ G.degree v }

/--
Erdős Problem #133 [Er97b], the page's explicit question: "does $f(n)/\sqrt{n}\to \infty$?" —
DISPROVED (answered no). The statement asserts that the ratio does not tend to infinity. It follows
from the Hanson–Seyffarth bound (`variants.ratio_bounded`, by `variants.main_of_ratio_bounded`).
The order of growth of $f(n)$ remains open; see `variants.alon_conjecture`.
-/
theorem erdos_problem_133 :
    ¬ Tendsto (fun n : ℕ => (erdos133_f n : ℝ) / Real.sqrt n) atTop atTop :=
  sorry

/--
Moore bound (PROVED, elementary): $f(n) \geq \lfloor\sqrt{n-1}\rfloor$ for all $n \geq 1$.

A graph with maximum degree $d$ and diameter $\leq 2$ has at most $1 + d + d(d-1) = d^2+1$
vertices, whether or not it is triangle-free. So a triangle-free graph on $n$ vertices of diameter
$\leq 2$ has maximum degree $d \geq \sqrt{n-1}$.
-/
theorem erdos_problem_133.variants.lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Nat.sqrt (n - 1) ≤ erdos133_f n :=
  sorry

/--
Hanson–Seyffarth upper bound [HaSe84] (PROVED, not checked here): $f(n) \leq (\sqrt{2} + o(1))\sqrt{n}$.

For every $\varepsilon > 0$ and all sufficiently large $n$, there is a triangle-free graph on $n$
vertices with diameter $\leq 2$ and maximum degree $\leq (\sqrt{2} + \varepsilon)\sqrt{n}$. The
construction is a Cayley graph on $\mathbb{Z}/n\mathbb{Z}$ with a symmetric complete sum-free
generating set of size $\sim \sqrt{n}$.
-/
theorem erdos_problem_133.variants.hanson_seyffarth :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ (Real.sqrt 2 + ε) * Real.sqrt n :=
  sorry

/--
Füredi–Seress improvement [FuSe94] (PROVED, not checked here):
$f(n) \leq (\frac{2}{\sqrt{3}} + o(1))\sqrt{n}$.
-/
theorem erdos_problem_133.variants.furedi_seress :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ (2 / Real.sqrt 3 + ε) * Real.sqrt n :=
  sorry

/--
The ratio $f(n)/\sqrt{n}$ is bounded (PROVED, not checked here): this is the Hanson–Seyffarth
construction read as $f(n) = O(\sqrt{n})$.
-/
theorem erdos_problem_133.variants.ratio_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (erdos133_f n : ℝ) ≤ C * Real.sqrt n :=
  sorry

/--
The main theorem follows from the bound $f(n) = O(\sqrt{n})$ (PROVED): a ratio that is eventually
at most $C$ cannot tend to infinity.
-/
theorem erdos_problem_133.variants.main_of_ratio_bounded
    (h : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, (erdos133_f n : ℝ) ≤ C * Real.sqrt n) :
    ¬ Tendsto (fun n : ℕ => (erdos133_f n : ℝ) / Real.sqrt n) atTop atTop := by
  intro ht
  obtain ⟨C, hC, hev⟩ := h
  have h1 := ht.eventually_gt_atTop C
  obtain ⟨n, hn1, hn2, hn3⟩ := (hev.and (h1.and (eventually_ge_atTop 1))).exists
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn3)
  have : (erdos133_f n : ℝ) / Real.sqrt n ≤ C := by
    rw [div_le_iff₀ hsq]
    exact hn1
  linarith

/--
Alon's conjecture (OPEN; the page: "Alon believes that the truth is $f(n)\sim \sqrt{n}$"):
$f(n)/\sqrt{n} \to 1$. The known bounds are $f(n) \geq (1 - o(1))\sqrt{n}$ and
$f(n) \leq (\frac{2}{\sqrt{3}} + o(1))\sqrt{n}$.
-/
theorem erdos_problem_133.variants.alon_conjecture :
    Tendsto (fun n : ℕ => (erdos133_f n : ℝ) / Real.sqrt n) atTop (nhds 1) :=
  sorry

/--
A check that the corrected definition is not degenerate (PROVED in Lean): $f(2) = 1$. The only graph
on two vertices that has diameter at most $2$ is $K_2$, which is triangle-free with maximum
degree $1$.
-/
theorem erdos_problem_133.variants.f_two : erdos133_f 2 = 1 := by
  unfold erdos133_f
  have h1 : 1 ∈ { k : ℕ | ∀ (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj],
      ¬HasTriangle G → HasDiameterAtMostTwo G → ∃ v : Fin 2, k ≤ G.degree v } := by
    intro G _ _ hd
    have hadj : G.Adj 0 1 := by
      rcases hd 0 1 (by decide) with h | ⟨w, h0, h1⟩
      · exact h
      · fin_cases w
        · exact absurd h0 (G.loopless.irrefl 0)
        · exact absurd h1 (G.loopless.irrefl 1)
    exact ⟨0, (SimpleGraph.degree_pos_iff_exists_adj G 0).mpr ⟨1, hadj⟩⟩
  have hbdd : ∀ k ∈ { k : ℕ | ∀ (G : SimpleGraph (Fin 2)) [DecidableRel G.Adj],
      ¬HasTriangle G → HasDiameterAtMostTwo G → ∃ v : Fin 2, k ≤ G.degree v }, k ≤ 1 := by
    intro k hk
    have hT : ¬HasTriangle (⊤ : SimpleGraph (Fin 2)) := by
      rintro ⟨a, b, c, hab, hbc, hac⟩
      simp only [SimpleGraph.top_adj] at hab hbc hac
      omega
    have hD : HasDiameterAtMostTwo (⊤ : SimpleGraph (Fin 2)) := by
      intro u v huv
      left
      simpa using huv
    obtain ⟨v, hv⟩ := hk ⊤ hT hD
    have : (⊤ : SimpleGraph (Fin 2)).degree v = 1 := by
      fin_cases v <;> simp
    omega
  apply le_antisymm
  · exact csSup_le ⟨1, h1⟩ hbdd
  · exact le_csSup ⟨1, hbdd⟩ h1

/-- The first pass's definition, kept to state its defect: the `sInf` of a set that is closed
    downwards and contains $0$. -/
noncomputable def erdos133_f_first_pass (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ¬HasTriangle G → HasDiameterAtMostTwo G →
    ∃ v : Fin n, k ≤ G.degree v }

/--
The first pass's `erdos133_f` is identically $0$ (PROVED in Lean). For $n\ge1$ the set contains
$0$, so its `sInf` is $0$. For $n=0$ the set is empty, and `sInf ∅ = 0`.
-/
theorem erdos_problem_133.variants.first_pass_f_eq_zero (n : ℕ) : erdos133_f_first_pass n = 0 := by
  unfold erdos133_f_first_pass
  by_cases hn : n = 0
  · subst hn
    have hempty : { k : ℕ | ∀ (G : SimpleGraph (Fin 0)) [DecidableRel G.Adj],
        ¬HasTriangle G → HasDiameterAtMostTwo G → ∃ v : Fin 0, k ≤ G.degree v } = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨v, _⟩ := @h ⊥ (fun a b => Classical.dec _)
        (fun ⟨a, _⟩ => a.elim0) (fun u => u.elim0)
      exact v.elim0
    rw [hempty]
    exact Nat.sInf_empty
  · apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    intro G _ _ _
    exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩, Nat.zero_le _⟩

/--
With the first pass's definition the Moore lower bound is false (PROVED in Lean): at $n=2$ it
reads $1\le0$.
-/
theorem erdos_problem_133.variants.first_pass_lower_bound_false :
    ¬ (∀ n : ℕ, 1 ≤ n → Nat.sqrt (n - 1) ≤ erdos133_f_first_pass n) := by
  intro h
  have := h 2 (by norm_num)
  rw [erdos_problem_133.variants.first_pass_f_eq_zero] at this
  norm_num at this

/--
With the first pass's definition Alon's conjecture is false (PROVED in Lean): the ratio is
identically $0$, so it cannot tend to $1$.
-/
theorem erdos_problem_133.variants.first_pass_alon_false :
    ¬ Tendsto (fun n : ℕ => (erdos133_f_first_pass n : ℝ) / Real.sqrt n) atTop (nhds 1) := by
  intro h
  have h0 : (fun n : ℕ => (erdos133_f_first_pass n : ℝ) / Real.sqrt n) = fun _ => 0 := by
    funext n
    simp [erdos_problem_133.variants.first_pass_f_eq_zero]
  rw [h0] at h
  have := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at this
