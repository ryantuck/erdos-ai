-- [AI - Claude Sonnet 5.5]: Erdős Problem 151 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #151: The clique transversal number and $n-H(n)$

*Source:* [erdosproblems.com/151](https://www.erdosproblems.com/151) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; page last edited 2 December 2025; captured 2026-02-20 as the page and as the
tidied problem box, with identical content). [Er88, p.82] [EGT92, p.280]

For a graph $G$ let $\tau(G)$ denote the minimal number of vertices that include at least one from each maximal
clique of $G$ on at least two vertices (sometimes called the clique transversal number).

Let $H(n)$ be maximal such that every triangle-free graph on $n$ vertices contains an independent set on $H(n)$
vertices.

If $G$ is a graph on $n$ vertices then is $\tau(G)\leq n-H(n)$?

Remarks recorded on the page:
* It is easy to see that $\tau(G) \leq n-\sqrt{n}$. Note also that if $G$ is triangle-free then trivially
  $\tau(G)\leq n-H(n)$.
* This is listed in [Er88] as a problem of Erdős and Gallai, who were unable to make progress even assuming $G$ is
  $K_4$-free. There Erdős remarked that this conjecture is 'perhaps completely wrongheaded'.
* It later appeared as Problem 1 in [EGT92].
* The general behaviour of $\tau(G)$ is the subject of [610].

Tags: graph theory. OEIS: "Possible". 1 comment at capture (not captured).

**Status.** OPEN. The mirror (`teorth/erdosproblems`) has `open` since 2025-08-31, no prize. Upstream has no
`151.lean`.

**Encoding.**
* `IsMaximalCliqueFS G S` says that `S` is an inclusion-maximal clique. `IsCliqueTransversal G T` says that `T` meets
  every maximal clique with at least two vertices, so isolated vertices (maximal cliques with one vertex) are not
  hit, as on the page. `cliqueTransversalNumber G` is the least size of such a `T`; `Finset.univ` is one, so the set of
  sizes is nonempty and `sInf` is its least element.
* `H n` is the minimum independence number of a triangle-free graph on `Fin n`, which is the page's "maximal such
  that every triangle-free graph contains an independent set on `H n` vertices". The edgeless graph is triangle-free,
  so the set is nonempty. In terms of the Ramsey numbers $R(3,k)$, $H(n)=\max\{k:R(3,k)\le n\}$; exact search gives
  $H(n)=1,1,2,2,2,3,3$ for $n=1,\dots,7$, and $H(8)=3$ since $R(3,4)=9$.
* `n - H n` is subtraction of natural numbers. It is exact, since `variants.H_le` proves `H n ≤ n`.
* `variants.tau_le_sub_independenceNumber` proves $\tau(G)\le n-\alpha(G)$ for every graph, and
  `variants.triangle_free_case` the page's "trivially": $\tau(G)\le n-H(n)$ for triangle-free $G$.
* The remark "$\tau(G)\le n-\sqrt n$" cannot hold literally for every $n$: it fails at $n=2$ for $K_2$
  (`variants.tau_le_sqrt_false`, proved in Lean) and at $n=5$ for $C_5$ ($\tau=3>5-\sqrt5$, found by exhaustive
  search). It is an asymptotic remark, and v2 states the form with an additive constant: `variants.easy_bound`, which
  follows from the bound $\tau(G)\le n-\sqrt{2n}+O(1)$ that the page of [610] attributes to [EGT92]
  (`variants.erdos_gallai_tuza`). **DEFERRED:** the exact form of the easy bound in [EGT92].
* The $K_4$-free case, in which Erdős and Gallai could make no progress, is `variants.k4_free`. This is an editorial
  variant.
* Exhaustive search over all labelled graphs on at most 8 vertices finds $\tau(G)\le n-H(n)$ for every graph, with
  equality for the maximum of $\tau$ at every $n\le8$.

## References

* [Er88] Erdős, P., _Problems and results in combinatorial analysis and graph theory_. Discrete Math. (1988), 81–92.
* [EGT92] Erdős, P., Gallai, T. and Tuza, Zs., _Covering the cliques of a graph with vertices_. Discrete Math.
  (1992), 279–289.
* [610] The cross-reference of the page: Erdős Problem #610, whose page says that a positive answer to it would follow
  from a positive answer to this problem, since Ajtai, Komlós and Szemerédi [AKS80] proved $H(n)\gg\sqrt{n\log n}$.
  [AKS80] is cited on the page of [610]. **DEFERRED:** no bibliographic data was recovered for it.

(Provenance: [Er88] and [EGT92] are from the `/latex/151` fetch in the session logs.)
-/

/-- S is a maximal clique of G (represented as a Finset): it is a clique and
    no vertex outside S can be added while preserving the clique property. -/
def IsMaximalCliqueFS {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsClique (S : Set (Fin n)) ∧
  ∀ v : Fin n, v ∉ S → ¬G.IsClique (↑(insert v S) : Set (Fin n))

/-- T is a clique transversal of G if T has non-empty intersection with every
    maximal clique of G that has at least 2 vertices. -/
def IsCliqueTransversal {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), IsMaximalCliqueFS G S → 2 ≤ S.card → (T ∩ S).Nonempty

/-- The clique transversal number τ(G): the minimum cardinality of a clique
    transversal of G. -/
noncomputable def cliqueTransversalNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k }

/-- S is an independent set in G: no two distinct vertices of S are adjacent. -/
def IsIndependentSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- The independence number α(G): the maximum cardinality of an independent set. -/
noncomputable def independenceNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = k }

/-- H(n) is maximal such that every triangle-free graph on n vertices contains
    an independent set of size H(n); equivalently, H(n) is the minimum
    independence number over all triangle-free graphs on n vertices. -/
noncomputable def H (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ independenceNumber G = k }

/--
Erdős Problem #151 [Er88, p.82] [EGT92, p.280] (problem of Erdős and Gallai) — OPEN:
If G is a graph on n vertices then τ(G) ≤ n - H(n),
where τ(G) is the clique transversal number of G and H(n) is the maximum k
such that every triangle-free graph on n vertices contains an independent set
of size k.
-/
theorem erdos_problem_151 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      cliqueTransversalNumber G ≤ n - H n :=
  sorry

/-- The sizes of independent sets are bounded by `n` (PROVED in Lean). -/
theorem erdos_problem_151.indep_bddAbove {n : ℕ} (G : SimpleGraph (Fin n)) :
    BddAbove { k : ℕ | ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = k } := by
  refine ⟨n, ?_⟩
  rintro k ⟨S, -, rfl⟩
  simpa using Finset.card_le_univ S

/-- A maximum independent set exists, so `independenceNumber` is a true maximum (PROVED in Lean). -/
theorem erdos_problem_151.exists_max_indep {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = independenceNumber G := by
  have hne : { k : ℕ | ∃ S : Finset (Fin n), IsIndependentSet G S ∧ S.card = k }.Nonempty :=
    ⟨0, ∅, fun u v hu => absurd hu (by simp), rfl⟩
  exact Nat.sSup_mem hne (erdos_problem_151.indep_bddAbove G)

/-- `α(G) ≤ n` (PROVED in Lean). -/
theorem erdos_problem_151.independenceNumber_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    independenceNumber G ≤ n := by
  obtain ⟨S, -, hS⟩ := erdos_problem_151.exists_max_indep G
  rw [← hS]
  simpa using Finset.card_le_univ S

/-- The edgeless graph on `n` vertices has independence number `n` (PROVED in Lean). -/
theorem erdos_problem_151.independenceNumber_bot (n : ℕ) :
    independenceNumber (⊥ : SimpleGraph (Fin n)) = n := by
  apply le_antisymm (erdos_problem_151.independenceNumber_le _)
  have h : n ∈ { k : ℕ | ∃ S : Finset (Fin n),
      IsIndependentSet (⊥ : SimpleGraph (Fin n)) S ∧ S.card = k } :=
    ⟨Finset.univ, fun u v _ _ _ => by simp, by simp⟩
  exact le_csSup (erdos_problem_151.indep_bddAbove _) h

/-- `H n ≤ n` (PROVED in Lean), so the subtraction `n - H n` of the main theorem is exact. -/
theorem erdos_problem_151.variants.H_le (n : ℕ) : H n ≤ n := by
  have h : n ∈ { k : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ independenceNumber G = k } :=
    ⟨⊥, by simp, erdos_problem_151.independenceNumber_bot n⟩
  exact Nat.sInf_le h

/--
`τ(G) ≤ n - α(G)` for every graph (PROVED in Lean): the complement of a maximum independent set meets every maximal
clique with at least two vertices, since such a clique has at most one vertex in the independent set.
-/
theorem erdos_problem_151.variants.tau_le_sub_independenceNumber {n : ℕ} (G : SimpleGraph (Fin n)) :
    cliqueTransversalNumber G ≤ n - independenceNumber G := by
  obtain ⟨S, hS, hcard⟩ := erdos_problem_151.exists_max_indep G
  have hT : IsCliqueTransversal G (Finset.univ \ S) := by
    intro C hC h2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < C.card)
    have hadj : G.Adj u v := hC.1 (by exact_mod_cast hu) (by exact_mod_cast hv) huv
    by_cases hus : u ∈ S
    · have hvs : v ∉ S := fun hvs => hS u v hus hvs huv hadj
      exact ⟨v, Finset.mem_inter.mpr ⟨by simp [hvs], hv⟩⟩
    · exact ⟨u, Finset.mem_inter.mpr ⟨by simp [hus], hu⟩⟩
  have hmem : (n - independenceNumber G) ∈
      { k : ℕ | ∃ T : Finset (Fin n), IsCliqueTransversal G T ∧ T.card = k } := by
    refine ⟨Finset.univ \ S, hT, ?_⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin,
      hcard]
  exact Nat.sInf_le hmem

/-- The page's "trivially": for a triangle-free graph, `τ(G) ≤ n - H(n)` (PROVED in Lean). -/
theorem erdos_problem_151.variants.triangle_free_case {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : cliqueTransversalNumber G ≤ n - H n := by
  have h1 : H n ≤ independenceNumber G := Nat.sInf_le ⟨G, hG, rfl⟩
  calc cliqueTransversalNumber G ≤ n - independenceNumber G :=
        erdos_problem_151.variants.tau_le_sub_independenceNumber G
    _ ≤ n - H n := Nat.sub_le_sub_left h1 n

/-- The clique transversal number of `K₂` is at least `1` (PROVED in Lean): `{0, 1}` is a maximal clique. -/
theorem erdos_problem_151.cliqueTransversalNumber_k2 :
    1 ≤ cliqueTransversalNumber (⊤ : SimpleGraph (Fin 2)) := by
  have hne : { k : ℕ | ∃ T : Finset (Fin 2),
      IsCliqueTransversal (⊤ : SimpleGraph (Fin 2)) T ∧ T.card = k }.Nonempty := by
    refine ⟨(Finset.univ : Finset (Fin 2)).card, Finset.univ, ?_, rfl⟩
    intro S _ h2
    have : S.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨T, hT, hcard⟩ := Nat.sInf_mem hne
  have hmax : IsMaximalCliqueFS (⊤ : SimpleGraph (Fin 2)) {0, 1} := by
    refine ⟨?_, ?_⟩
    · intro u hu v hv huv
      simpa using huv
    · intro v hv
      exfalso
      fin_cases v <;> simp at hv
  obtain ⟨x, hx⟩ := hT {0, 1} hmax (by decide)
  have : 0 < T.card := Finset.card_pos.mpr ⟨x, (Finset.mem_inter.mp hx).1⟩
  unfold cliqueTransversalNumber
  omega

/--
The page's remark "it is easy to see that `τ(G) ≤ n - √n`" is false as stated for `n = 2` (PROVED in Lean): `K₂` has
`τ = 1 > 2 - √2`. (It also fails at `n = 5` for `C₅`, by exhaustive search.) The remark holds up to an additive
constant, `variants.easy_bound`.
-/
theorem erdos_problem_151.variants.tau_le_sqrt_false :
    ¬ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (cliqueTransversalNumber G : ℝ) ≤ n - Real.sqrt n := by
  intro h
  have h2 := h 2 ⊤
  have h1 : (1 : ℝ) ≤ cliqueTransversalNumber (⊤ : SimpleGraph (Fin 2)) := by
    exact_mod_cast erdos_problem_151.cliqueTransversalNumber_k2
  have hs : (1 : ℝ) < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  push_cast at h2
  linarith

/--
Erdős, Gallai and Tuza [EGT92] (PROVED, not checked here), as recorded on the page of [610]:
`τ(G) ≤ n - √(2n) + O(1)`. **DEFERRED:** the page of this problem does not state it.
-/
theorem erdos_problem_151.variants.erdos_gallai_tuza :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (cliqueTransversalNumber G : ℝ) ≤ n - Real.sqrt (2 * n) + C :=
  sorry

/--
The page's easy bound, with the additive constant it needs: `τ(G) ≤ n - √n + O(1)` (PROVED in Lean from
`variants.erdos_gallai_tuza`).
-/
theorem erdos_problem_151.variants.easy_bound :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (cliqueTransversalNumber G : ℝ) ≤ n - Real.sqrt n + C := by
  obtain ⟨C, hC⟩ := erdos_problem_151.variants.erdos_gallai_tuza
  refine ⟨C, fun n G => ?_⟩
  have h1 := hC n G
  have h2 : Real.sqrt n ≤ Real.sqrt (2 * n) :=
    Real.sqrt_le_sqrt (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  linarith

/--
The `K₄`-free case (OPEN, an editorial variant): Erdős and Gallai "were unable to make progress even assuming `G` is
`K₄`-free". For triangle-free graphs the inequality is trivial (`variants.triangle_free_case`).
-/
theorem erdos_problem_151.variants.k4_free :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 →
      cliqueTransversalNumber G ≤ n - H n :=
  sorry

end
