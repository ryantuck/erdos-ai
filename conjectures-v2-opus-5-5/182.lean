-- [AI - Claude Opus 5.5]: Erdős Problem 182 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #182

*Source:* [erdosproblems.com/182](https://www.erdosproblems.com/182) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 23 January 2026). [Er75] [Er81]

Let $k\geq 3$. What is the maximum number of edges that a graph on $n$ vertices can contain if it
does not have a $k$-regular subgraph? Is it $\ll n^{1+o(1)}$?

Remarks recorded on the page (abridged): asked by Erdős and Sauer. Resolved by Janzer and Sudakov
[JaSu23], who proved that there exists some $C=C(k)>0$ such that any graph on $n$ vertices with at
least $Cn\log\log n$ edges contains a $k$-regular subgraph. Chakraborti, Janzer, Methuku, and
Montgomery [CJMM24b] have shown that one can take $C(k)\ll k^2$, which is the best possible up to
an absolute constant. A construction due to Pyber, Rödl, and Szemerédi [PRS95] shows that this is
best possible. In [Er75] Erdős mentions a similar question of Szemerédi, in which the $k$-regular
subgraph must be connected; if $F(n,k)$ is the smallest number of edges on $n$ vertices which
guarantees a connected $k$-regular subgraph, Erdős [Er75] proved $F(n,3)\ll n^{5/3}$.

Later fetches (2026-03-10 and the 2026-03-15 `/latex/182`) also record a \$100 prize offered in
[Er78] for the case $k=3$; the 2026-02-20 capture does not mention it.

## Encoding notes

* The main theorem is the Janzer–Sudakov theorem. It answers the page's question in the
  affirmative: `variants.question_of_main` (PROVED in Lean) derives "every graph with at least
  $n^{1+\varepsilon}$ edges contains a $k$-regular subgraph, for large $n$" from it. With
  [PRS95], the maximum is $\Theta_k(n\log\log n)$.
* A $k$-regular subgraph is an injective homomorphic image of a nonempty finite $k$-regular graph,
  so it need not be induced. The nonemptiness condition matters: without it the empty graph would be
  a $k$-regular subgraph of everything. Sanity checks (PROVED in Lean): every graph on a nonempty
  vertex type has a $0$-regular subgraph, the edgeless graph has no $k$-regular subgraph for
  `k ≥ 1`, and $K_{k+1}$ has a $k$-regular subgraph.

## References

From the site's `/latex/182` bibliography:
* [CJMM24b] Chakraborti, D., Janzer, O., Methuku, A. and Montgomery, R., _Regular subgraphs at
  every density_. arXiv:2411.11785 (2024).
* [Er75] Erdős, P., _Some recent progress on extremal problems in graph theory_. Congressus
  Numerantium (1975), 3–14.
* [Er78] Erdős, Paul, _Problems and results in combinatorial analysis and combinatorial number
  theory_. Proceedings of the Ninth Southeastern Conference on Combinatorics, Graph Theory, and
  Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978), 29–40.
* [JaSu23] Janzer, Oliver and Sudakov, Benny, _Resolution of the Erdős–Sauer problem on regular
  subgraphs_. Forum Math. Pi (2023), Paper No. e19, 13.
* [PRS95] Pyber, L., Rödl, V. and Szemerédi, E., _Dense graphs without 3-regular subgraphs_.
  J. Combin. Theory Ser. B (1995), 41–54.

Other sources:
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_.
  Combinatorica (1981), 25–42. (Site `/latex/111`; the `/latex/182` fetch lists no entry for it.)

*Provenance:* second pass of `conjectures/182.lean` (Opus 5.5 review, `opus-5-5-review/182.md`).
-/

/-- G contains a k-regular subgraph: there exists a nonempty finite graph H that
    is k-regular (every vertex has degree exactly k) and admits an injective
    graph homomorphism into G. -/
def containsKRegularSubgraph182 {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (U : Type) (fU : Fintype U) (_ : Nonempty U) (H : SimpleGraph U) (dH : DecidableRel H.Adj),
    haveI := fU; haveI := dH;
    (∀ v : U, H.degree v = k) ∧
    ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #182 (Erdős-Sauer conjecture) [Er75, Er81]:

For every k ≥ 3, there exists a constant C > 0 such that for all sufficiently
large n, every simple graph on n vertices with at least C · n · log(log(n))
edges contains a k-regular subgraph.

Proved by Janzer and Sudakov [JaSu23]. (Status: PROVED; the true direction.)
-/
theorem erdos_problem_182 :
    ∀ k : ℕ, 3 ≤ k →
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ,
    ∀ (n : ℕ), n₀ ≤ n →
    ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) * Real.log (Real.log (n : ℝ)) →
      containsKRegularSubgraph182 G k :=
  sorry

/-- Sanity check (PROVED in Lean): a single vertex is a `0`-regular subgraph of any graph on a
nonempty vertex type. -/
theorem erdos_problem_182.containsKRegularSubgraph182_zero {V : Type*} [Nonempty V]
    (G : SimpleGraph V) : containsKRegularSubgraph182 G 0 := by
  obtain ⟨x⟩ := ‹Nonempty V›
  refine ⟨Unit, inferInstance, inferInstance, ⊥, inferInstance, fun v => ?_, fun _ => x,
    fun a b _ => Subsingleton.elim a b, fun u v h => absurd h (by simp)⟩
  simp

/-- Sanity check (PROVED in Lean): for `k ≥ 1` the edgeless graph has no `k`-regular subgraph. -/
theorem erdos_problem_182.not_containsKRegularSubgraph182_bot {V : Type*} {k : ℕ} (hk : 1 ≤ k) :
    ¬ containsKRegularSubgraph182 (⊥ : SimpleGraph V) k := by
  rintro ⟨U, fU, ⟨u⟩, H, dH, hdeg, f, -, hf⟩
  have hpos : 0 < H.degree u := by rw [hdeg u]; omega
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj u).1 hpos
  exact hf u w hw

/-- Sanity check (PROVED in Lean): the complete graph $K_{k+1}$ is itself a `k`-regular subgraph. -/
theorem erdos_problem_182.containsKRegularSubgraph182_complete (k : ℕ) :
    containsKRegularSubgraph182 (⊤ : SimpleGraph (Fin (k + 1))) k := by
  refine ⟨Fin (k + 1), inferInstance, inferInstance, ⊤, inferInstance, fun v => ?_, id,
    Function.injective_id, fun u v h => h⟩
  simp

/-- The main theorem answers the page's question in the affirmative (PROVED in Lean): for every
`k ≥ 3` and `ε > 0`, every graph on `n` vertices with at least $n^{1+\varepsilon}$ edges contains a
`k`-regular subgraph once `n` is large, i.e. the maximum is $\ll n^{1+o(1)}$. -/
theorem erdos_problem_182.variants.question_of_main
    (h : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj), haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) * Real.log (Real.log (n : ℝ)) →
      containsKRegularSubgraph182 G k) :
    ∀ k : ℕ, 3 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj), haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ (n : ℝ) ^ (1 + ε) →
      containsKRegularSubgraph182 G k := by
  intro k hk ε hε
  obtain ⟨C, hC, n₀, hn₀⟩ := h k hk
  have hlog : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1 / C) * x ^ ε := by
    filter_upwards [(isLittleO_log_rpow_atTop hε).bound (by positivity : (0 : ℝ) < 1 / C),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) ε)] at hx
    exact hx
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.1 (tendsto_natCast_atTop_atTop.eventually hlog)
  refine ⟨max n₀ (max n₁ 2), fun n hn G dG hE =>
    hn₀ n (le_of_max_le_left hn) G dG (le_trans ?_ hE)⟩
  have hn2 : (2 : ℝ) ≤ n := by
    exact_mod_cast le_trans (le_max_right _ _) (le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have h1 : Real.log (Real.log n) ≤ Real.log n :=
    (Real.log_le_sub_one_of_pos hlogn).trans (by linarith)
  have h2 : Real.log n ≤ (1 / C) * (n : ℝ) ^ ε :=
    hn₁ n (le_trans (le_max_left _ _) (le_of_max_le_right hn))
  have h4 : C * Real.log (Real.log n) ≤ (n : ℝ) ^ ε := by
    have h5 := mul_le_mul_of_nonneg_left (h1.trans h2) hC.le
    rwa [← mul_assoc, mul_one_div_cancel hC.ne', one_mul] at h5
  rw [Real.rpow_add hnpos, Real.rpow_one]
  calc C * (n : ℝ) * Real.log (Real.log n) = n * (C * Real.log (Real.log n)) := by ring
    _ ≤ n * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_left h4 hnpos.le

/-- Chakraborti, Janzer, Methuku and Montgomery [CJMM24b] (SOLVED; not proved here): one can take
$C(k)\ll k^2$. -/
theorem erdos_problem_182.variants.cjmm :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 3 ≤ k → ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj), haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ A * (k : ℝ) ^ 2 * (n : ℝ) * Real.log (Real.log (n : ℝ)) →
      containsKRegularSubgraph182 G k :=
  sorry

/-- Pyber, Rödl and Szemerédi [PRS95] (SOLVED; not proved here): the main theorem is best possible
up to the constant. As recorded on the page, for each `k ≥ 3` there are arbitrarily large graphs
with $\gg n\log\log n$ edges and no `k`-regular subgraph. -/
theorem erdos_problem_182.variants.pyber_rodl_szemeredi :
    ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧
      ∃ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj), haveI := dG;
        (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ∧
        ¬ containsKRegularSubgraph182 G k :=
  sorry

/-- `G` contains a connected `k`-regular subgraph: as `containsKRegularSubgraph182`, with the
witness graph connected (Szemerédi's variant). -/
def containsConnectedKRegularSubgraph182 {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (U : Type) (fU : Fintype U) (H : SimpleGraph U) (dH : DecidableRel H.Adj),
    haveI := fU; haveI := dH;
    H.Connected ∧ (∀ v : U, H.degree v = k) ∧
    ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- Szemerédi's connected variant: Erdős [Er75] proved $F(n,3)\ll n^{5/3}$ (SOLVED; not proved
here), i.e. $\gg n^{5/3}$ edges force a connected `3`-regular subgraph. -/
theorem erdos_problem_182.variants.connected_three :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj), haveI := dG;
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ) ^ ((5 : ℝ) / 3) →
      containsConnectedKRegularSubgraph182 G 3 :=
  sorry

end
