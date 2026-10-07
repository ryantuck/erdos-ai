-- [AI - Claude Sonnet 5.5]: Erdős Problem 159 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Circulant

open SimpleGraph

/-!
# Erdős Problem #159: $R(C_4,K_n)\ll n^{2-c}$ for some $c>0$

*Source:* [erdosproblems.com/159](https://www.erdosproblems.com/159) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; captured 2026-02-20 as the page and as the tidied problem box, in two sessions with
identical content; the page then showed no edit date, "Formalised statement? No", 0 comments, the OEIS field "Possible" and
no prize). [Er81][Er84d]

There exists some constant $c>0$ such that
$$R(C_4,K_n) \ll n^{2-c}.$$

Remarks recorded on the page: The current bounds are
$$\frac{n^{3/2}}{(\log n)^{3/2}}\ll R(C_4,K_n)\ll \frac{n^2}{(\log n)^2}.$$
The upper bound is due to Szemerédi (mentioned in [EFRS78]), and the lower bound is due to Spencer [Sp77]. This problem is
#17 in Ramsey Theory in the graphs problem collection.

Tags: graph theory, ramsey theory.

**Status.** OPEN. The page changed after the capture: fetches of 2026-03-10 and later show a prize of \$100 offered by
Erdős in [Er78, p. 34] for a proof or disproof, and upstream's docstring says the same. The mirror clone
(`teorth/erdosproblems`, `b916d95`) has `open` since 2025-08-31 and `prize: no`, so it predates that edit. Upstream's
`159.lean` (`df3f12d`) has `erdos_159` as `research open`, as a direct assertion with
`SimpleGraph.graphRamsey (cycleGraph 4) (completeGraph (Fin n))`.

**Encoding.**
* `containsSubgraph G H` says there is an injective map `f` with `H.Adj u v → G.Adj (f u) (f v)`, that is, `G` contains a
  copy of `H` as a (not necessarily induced) subgraph. `variants.containsSubgraph_iff` proves in Lean that this is Mathlib's
  `H ⊑ G`.
* `C4` is the 4-cycle on `Fin 4`; `variants.C4_eq_cycleGraph` proves that it is Mathlib's `cycleGraph 4`.
* `ramseyC4Kn n` is the least `N` such that every graph on `N` vertices contains `C₄` or has an independent set of size `n`
  (its complement contains `Kₙ`; `variants.independent_iff` proves that this is an injective map from `Fin n` to pairwise
  non-adjacent vertices). `variants.ramseyC4Kn_eq` proves that this is the definition upstream uses
  (`graphRamsey (cycleGraph 4) (completeGraph (Fin n))`). The `sInf` of an empty set would be `0`; the set is nonempty by
  Ramsey's theorem (this is not formalized), and `variants.ramseyC4Kn_zero`, `ramseyC4Kn_one` and `ramseyC4Kn_two` evaluate
  the definition for `n = 0, 1, 2`: `0`, `1` and `4`.
* The statement says: there are `c > 0`, `C > 0` and `N₀` with `R(C₄, Kₙ) ≤ C n^(2-c)` for all `n ≥ N₀`, with the real power
  `(n : ℝ) ^ (2 - c)`. `variants.main_iff_all_n` proves that `N₀` can be dropped (all `n ≥ 1`), which is upstream's form. The page states the problem as an assertion and the input asserts it, which is the asked direction.
  By the lower bound of Spencer only `c ≤ 1/2` can hold.
* `variants.szemeredi_upper` and `variants.spencer_lower` record the page's two bounds, with `sorry`. They are SOLVED in the
  literature (the upper bound is attributed to Szemerédi, "mentioned in [EFRS78]") and are not proved here. **DEFERRED:**
  the papers were not seen.

## References

* [Er78] Erdős, P., _Problems and results in combinatorial analysis and combinatorial number theory_. Proc. Ninth Southeastern
  Conf. Combinatorics, Graph Theory, and Computing (Florida Atlantic Univ., Boca Raton, Fla., 1978), 29–40. (From the
  `/latex/159` fetch in the session logs.)
* [Er81] Erdős, P., _On the combinatorial problems which I would most like to see solved_. Combinatorica (1981), 25–42. (From
  other problems' `/latex` fetches, for example `/latex/111`.)
* [Er84d] Erdős, P., _Extremal problems in number theory, combinatorics and geometry_. Proc. International Congress of
  Mathematicians, Vol. 1, 2 (Warsaw, 1983) (1984), 51–70. (From the `/latex/772` fetch.)
* [EFRS78] Erdős, P., Faudree, R. J., Rousseau, C. C. and Schelp, R. H., _On cycle-complete graph Ramsey numbers_. J. Graph
  Theory (1978), 53–64. (From the `/latex/159` fetch.)
* [Sp77] Spencer, J., _Asymptotic lower bounds for Ramsey functions_. Discrete Math. (1977), 69–76. (From the `/latex/159`
  fetch.)
-/

/-- An injective graph homomorphism from H to G witnesses that G contains
    a subgraph isomorphic to H. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The 4-cycle C₄: vertices Fin 4, with i adjacent to j iff they are
    consecutive modulo 4 (i.e., the edges are 0–1, 1–2, 2–3, 3–0). -/
def C4 : SimpleGraph (Fin 4) where
  Adj i j := (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := ⟨by intro i; fin_cases i <;> decide⟩

/-- The graph Ramsey number R(C₄, Kₙ): the minimum N such that every simple
    graph G on N vertices either contains a copy of C₄ as a subgraph, or the
    complement Gᶜ contains a copy of Kₙ (i.e., G has an independent set of
    size n). -/
noncomputable def ramseyC4Kn (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin n))}

/--
Erdős Conjecture (Problem #159) [Er81, Er84d] (OPEN):

There exists a constant c > 0 such that R(C₄, Kₙ) ≪ n^{2-c}, i.e.,
R(C₄, Kₙ) = O(n^{2-c}) as n → ∞.

The Ramsey number R(C₄, Kₙ) is the minimum N such that every 2-colouring
of the edges of K_N contains a monochromatic C₄ in one colour or a
monochromatic Kₙ in the other colour.

The current bounds are:
  n^{3/2} / (log n)^{3/2} ≪ R(C₄, Kₙ) ≪ n² / (log n)²,
where the upper bound is due to Szemerédi [EFRS78] and the lower bound
to Spencer [Sp77]. Improving the upper bound to n^{2-c} for any fixed
c > 0 remains open.
-/
theorem erdos_problem_159 :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c) :=
  sorry

/-- `containsSubgraph G H` is Mathlib's `H ⊑ G`, containment as a subgraph (PROVED in Lean). -/
theorem erdos_problem_159.variants.containsSubgraph_iff {V U : Type*} (G : SimpleGraph V)
    (H : SimpleGraph U) : containsSubgraph G H ↔ H ⊑ G := by
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨⟨⟨f, fun {u v} h => hadj u v h⟩, hf⟩⟩
  · rintro ⟨c⟩
    exact ⟨c.toHom, c.injective, fun u v h => c.toHom.map_rel h⟩

/-- `C4` is Mathlib's `cycleGraph 4` (PROVED in Lean). -/
theorem erdos_problem_159.variants.C4_eq_cycleGraph : C4 = cycleGraph 4 := by
  ext i j
  rw [show cycleGraph 4 = cycleGraph (2 + 2) from rfl, cycleGraph_adj]
  fin_cases i <;> fin_cases j <;> simp [C4] <;> decide

/-- `Gᶜ` contains `Kₙ` as a subgraph iff `G` has `n` distinct pairwise non-adjacent vertices, that is, an independent set of
size `n` (PROVED in Lean), as the docstring of `ramseyC4Kn` says. -/
theorem erdos_problem_159.variants.independent_iff {N n : ℕ} (G : SimpleGraph (Fin N)) :
    containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin n)) ↔
    ∃ f : Fin n → Fin N, Function.Injective f ∧ ∀ i j, i ≠ j → ¬ G.Adj (f i) (f j) := by
  constructor
  · rintro ⟨f, hf, hadj⟩
    refine ⟨f, hf, fun i j hij => ?_⟩
    have := hadj i j (by simpa using hij)
    simpa [SimpleGraph.compl_adj] using this.2
  · rintro ⟨f, hf, hna⟩
    refine ⟨f, hf, fun i j hij => ?_⟩
    have hne : i ≠ j := hij.ne
    simp only [SimpleGraph.compl_adj]
    exact ⟨hf.ne hne, hna i j hne⟩

/-- `ramseyC4Kn` is the Ramsey number `graphRamsey (cycleGraph 4) (completeGraph (Fin n))` in the form of upstream's
definition, with Mathlib's containment relation `⊑` (PROVED in Lean). -/
theorem erdos_problem_159.variants.ramseyC4Kn_eq (n : ℕ) :
    ramseyC4Kn n = sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      cycleGraph 4 ⊑ G ∨ (⊤ : SimpleGraph (Fin n)) ⊑ Gᶜ} := by
  unfold ramseyC4Kn
  congr 1
  ext N
  simp only [Set.mem_setOf_eq, erdos_problem_159.variants.containsSubgraph_iff,
    erdos_problem_159.variants.C4_eq_cycleGraph]

/-- `R(C₄, K₀) = 0`: the empty graph on no vertices contains `K₀` in its complement (PROVED in Lean). -/
theorem erdos_problem_159.variants.ramseyC4Kn_zero : ramseyC4Kn 0 = 0 := by
  unfold ramseyC4Kn
  have h0 : (0 : ℕ) ∈ {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin 0))} := by
    intro G
    right
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun u => u.elim0⟩
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le h0)

/-- `R(C₄, K₁) = 1` (PROVED in Lean): a graph on one vertex has an independent set of size one, and the graph on no vertices
has neither a `C₄` nor a vertex. -/
theorem erdos_problem_159.variants.ramseyC4Kn_one : ramseyC4Kn 1 = 1 := by
  unfold ramseyC4Kn
  have h1 : (1 : ℕ) ∈ {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin 1))} := by
    intro G
    right
    refine ⟨id, Function.injective_id, fun u v huv => ?_⟩
    exact absurd (Subsingleton.elim u v) huv.ne
  have h0 : (0 : ℕ) ∉ {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin 1))} := by
    intro h
    rcases h ⊥ with ⟨f, -, -⟩ | ⟨f, -, -⟩
    · exact (f 0).elim0
    · exact (f 0).elim0
  have hmem := Nat.sInf_mem ⟨1, h1⟩
  have hne : sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin 1))} ≠ 0 := by
    intro h; rw [h] at hmem; exact h0 hmem
  have hle := Nat.sInf_le h1
  omega

/-- `R(C₄, K₂) = 4` (PROVED in Lean): every graph on four vertices has a non-adjacent pair or is the complete graph, which
contains `C₄`; the complete graph on three vertices has neither. -/
theorem erdos_problem_159.variants.ramseyC4Kn_two : ramseyC4Kn 2 = 4 := by
  unfold ramseyC4Kn
  have h4 : (4 : ℕ) ∈ {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
      containsSubgraph G C4 ∨ containsSubgraph Gᶜ (⊤ : SimpleGraph (Fin 2))} := by
    intro G
    by_cases h : ∃ u v : Fin 4, u ≠ v ∧ ¬ G.Adj u v
    · right
      obtain ⟨u, v, huv, hna⟩ := h
      refine ⟨![u, v], ?_, ?_⟩
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i j hij
        have hne : i ≠ j := hij.ne
        have hna' : ¬ G.Adj v u := fun h => hna h.symm
        fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.compl_adj, Ne.symm huv]
    · left
      push_neg at h
      exact ⟨id, Function.injective_id, fun u v huv => h u v huv.ne⟩
  apply le_antisymm (Nat.sInf_le h4)
  apply le_csInf ⟨4, h4⟩
  intro N hN
  by_contra hlt
  push_neg at hlt
  rcases hN ⊤ with ⟨f, hf, -⟩ | ⟨f, hf, hadj⟩
  · have := Fintype.card_le_of_injective f hf
    simp at this
    omega
  · have := hadj 0 1 (by decide)
    simp at this

/-- The threshold `N₀` can be dropped (PROVED in Lean): the main statement is equivalent to `R(C₄, Kₙ) ≤ C n^(2-c)` for all
`n ≥ 1`, which is upstream's form. For the finitely many `n < N₀` the constant is enlarged by the sum of the values, and `c`
is decreased to at most `1` so that `n^(2-c) ≥ 1`. -/
theorem erdos_problem_159.variants.main_iff_all_n :
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c)) ↔
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c)) := by
  constructor
  · rintro ⟨c, hc, C, hC, N₀, h⟩
    have hs : 0 ≤ ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    refine ⟨min c 1, lt_min hc one_pos, C + ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ),
      by linarith, fun n hn => ?_⟩
    have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ (2 - c) ≤ (n : ℝ) ^ (2 - min c 1) :=
      Real.rpow_le_rpow_of_exponent_le hnpos (by linarith [min_le_left c 1])
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ (2 - min c 1) :=
      Real.one_le_rpow hnpos (by linarith [min_le_right c 1])
    rcases le_or_gt N₀ n with hge | hlt
    · calc (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c) := h n hge
        _ ≤ C * (n : ℝ) ^ (2 - min c 1) := by gcongr
        _ ≤ (C + ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ)) * (n : ℝ) ^ (2 - min c 1) := by
            nlinarith
    · calc (ramseyC4Kn n : ℝ) ≤ ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ) :=
            Finset.single_le_sum (f := fun i => (ramseyC4Kn i : ℝ))
              (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr hlt)
        _ ≤ (C + ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ)) * 1 := by linarith
        _ ≤ (C + ∑ i ∈ Finset.range N₀, (ramseyC4Kn i : ℝ)) * (n : ℝ) ^ (2 - min c 1) := by
            gcongr
  · rintro ⟨c, hc, C, hC, h⟩
    exact ⟨c, hc, C, hC, 1, fun n hn => h n hn⟩

/-- Szemerédi's upper bound `R(C₄, Kₙ) ≪ n² / (log n)²` as the page states it (SOLVED in the literature, not proved
here). -/
theorem erdos_problem_159.variants.szemeredi_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (ramseyC4Kn n : ℝ) ≤ C * ((n : ℝ) ^ 2 / (Real.log (n : ℝ)) ^ 2) :=
  sorry

/-- Spencer's lower bound `n^(3/2) / (log n)^(3/2) ≪ R(C₄, Kₙ)` as the page states it (SOLVED in the literature, not proved
here). It shows that only `c ≤ 1/2` is possible in the main theorem. -/
theorem erdos_problem_159.variants.spencer_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * ((n : ℝ) ^ ((3 : ℝ) / 2) / (Real.log (n : ℝ)) ^ ((3 : ℝ) / 2)) ≤ (ramseyC4Kn n : ℝ) :=
  sorry
