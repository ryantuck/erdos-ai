-- [AI - Claude Opus 5.5]: Erdős Problem 163 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Erdős Problem #163

*Source:* [erdosproblems.com/163](https://www.erdosproblems.com/163) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 22 January 2026). [BuEr75] [Er82e]

For any $d\geq 1$ if $H$ is a graph such that every subgraph contains a vertex of degree at most
$d$ then $R(H)\ll_d n$.

Remarks recorded on the page:
* The Burr–Erdős conjecture. This is equivalent to showing that if $H$ is the union of $c$ forests
  then $R(H)\ll_c n$, and also that if every subgraph has average degree at most $d$ then
  $R(H)\ll_d n$.
* Solved by Lee [Le17], who proved that $R(H)\le 2^{2^{O(d)}}n$. More precisely, Lee proved that
  $R(H)\le 2^{d2^{O(\chi(H))}}n$. It is conjectured that $R(H)\le 2^{O(d)}n$.
* This problem is #9 in Ramsey Theory in the graphs problem collection. See also [800].

The input's statement is the true direction of a solved problem and is kept byte-identical.

## Encoding notes

* `containsCopy G H` is an injective homomorphism, which is Mathlib's `H ⊑ G`
  (`erdos_problem_163.containsCopy_iff`, PROVED). A 2-colouring of $K_N$ is a graph `G` on `Fin N`
  with its complement.
* `ramseyDiag H` is `sInf` of a set that Ramsey's theorem makes nonempty for every finite `H` (not
  formalized here). On the edgeless graph it gives the expected value $n$
  (`erdos_problem_163.ramseyDiag_bot`, PROVED).
* `IsDDegenerate H d` (every nonempty vertex set has a vertex with at most `d` neighbours inside it)
  is the usual degeneracy; checking induced subgraphs suffices, since passing to a subgraph only
  lowers degrees.
* The page's average-degree form follows from the main theorem
  (`variants.average_degree_of_main`, PROVED): a set whose degree sum is at most $d\lvert S\rvert$
  has a vertex of degree at most $d$.
* Graphs are taken on `Fin n`; every finite graph is isomorphic to one of these.

## References

* [BuEr75] Burr, S. A. and Erdős, P. Source of the conjecture. **DEFERRED:** no site bibliography
  entry was recovered. The archived DeepMind review and styled copy give _On the magnitude of
  generalized Ramsey numbers for graphs_, Infinite and finite sets, Vol. 1 (1975), 214–240 (which
  agrees with the model's recollection); upstream `formal-conjectures` (`df3f12d`) gives a different
  title, _On the Ramsey number of graphs with small degree-ratio_, Colloq. Math. Soc. János Bolyai
  (1975).
* [Er82e] Erdős, P., _Some of my favourite problems which recently have been solved_ (1982),
  59–79. (From the site's `/latex/71` bibliography.)
* [Le17] Lee, C., _Ramsey numbers of degenerate graphs_. Ann. of Math. (2) (2017), 791–829.
  (From the site's `/latex/163` bibliography; upstream gives volume 185.)

*Provenance:* second pass of `conjectures/163.lean` (Opus 5.5 review, `opus-5-5-review/163.md`).
-/

open SimpleGraph Finset

noncomputable section

/-- An injective graph homomorphism from H to G: G contains a (not necessarily
    induced) copy of H as a subgraph. -/
def containsCopy {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- A simple graph H on a finite vertex type is d-degenerate if every nonempty
    subset S of vertices contains a vertex v with at most d neighbours in S. -/
def IsDDegenerate {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (d : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty →
    ∃ v ∈ S, (S.filter (H.Adj v)).card ≤ d

/-- The diagonal Ramsey number R(H): the minimum N such that for every simple
    graph G on Fin N, either G or Gᶜ contains a copy of H. -/
noncomputable def ramseyDiag {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsCopy G H ∨ containsCopy Gᶜ H}

/--
Erdős Conjecture (Problem #163) [BuEr75, Er82e] — The Burr-Erdős Conjecture:

For every d ≥ 1, there exists a constant C_d > 0 such that for every
d-degenerate graph H on n vertices, R(H, H) ≤ C_d · n.

Equivalently, if H is the union of c forests then R(H) ≤ C_c · n.

Proved by Lee [Le17], who showed R(H) ≤ 2^{2^{O(d)}} · n.
(Status: PROVED; the statement is the true direction.)
-/
theorem erdos_problem_163 :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d →
      (ramseyDiag H : ℝ) ≤ C * (n : ℝ) :=
  sorry

/-- `containsCopy G H` is Mathlib's `H ⊑ G` (PROVED in Lean). -/
theorem erdos_problem_163.containsCopy_iff {V U : Type*} (G : SimpleGraph V)
    (H : SimpleGraph U) : containsCopy G H ↔ H ⊑ G := by
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨⟨⟨f, fun {u v} h => hadj u v h⟩, hf⟩⟩
  · rintro ⟨c⟩
    exact ⟨c.toHom, c.injective, fun u v h => c.toHom.map_rel h⟩

/-- The definition of `ramseyDiag` gives the expected value on the edgeless graph: a copy of
`⊥ : SimpleGraph (Fin n)` is just an injection, so `R(⊥) = n` (PROVED in Lean). -/
theorem erdos_problem_163.ramseyDiag_bot (n : ℕ) :
    ramseyDiag (⊥ : SimpleGraph (Fin n)) = n := by
  have key : {N : ℕ | ∀ G : SimpleGraph (Fin N),
      containsCopy G (⊥ : SimpleGraph (Fin n)) ∨ containsCopy Gᶜ (⊥ : SimpleGraph (Fin n))} =
      {N : ℕ | n ≤ N} := by
    ext N
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      rcases h ⊥ with ⟨f, hf, -⟩ | ⟨f, hf, -⟩ <;> simpa using Fintype.card_le_of_injective f hf
    · intro hN G
      exact Or.inl ⟨Fin.castLE hN, Fin.castLE_injective hN, fun u v h => absurd h (by simp)⟩
  unfold ramseyDiag
  rw [key]
  exact le_antisymm (Nat.sInf_le (le_refl n)) (le_csInf ⟨n, le_refl n⟩ fun b hb => hb)

/-- Degeneracy is monotone in `d` (PROVED in Lean). -/
theorem erdos_problem_163.isDDegenerate_mono {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d d' : ℕ} (hdd : d ≤ d')
    (h : IsDDegenerate H d) : IsDDegenerate H d' := by
  intro S hS
  obtain ⟨v, hv, hcard⟩ := h S hS
  exact ⟨v, hv, hcard.trans hdd⟩

/-- The page's equivalent form with average degrees follows from the main theorem: if every
nonempty `S` has degree sum (inside `S`) at most `d * |S|`, some vertex of `S` has at most `d`
neighbours in `S`, so the graph is `d`-degenerate (PROVED in Lean). -/
theorem erdos_problem_163.variants.average_degree_of_main
    (h : ∀ d : ℕ, 1 ≤ d →
      ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
      IsDDegenerate H d →
        (ramseyDiag H : ℝ) ≤ C * (n : ℝ)) :
    ∀ d : ℕ, 1 ≤ d →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    (∀ S : Finset (Fin n), S.Nonempty → ∑ v ∈ S, (S.filter (H.Adj v)).card ≤ d * S.card) →
      (ramseyDiag H : ℝ) ≤ C * (n : ℝ) := by
  intro d hd
  obtain ⟨C, hC, hH⟩ := h d hd
  refine ⟨C, hC, fun n H _ havg => hH n H ?_⟩
  intro S hS
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ v ∈ S, d = d * S.card := by
    rw [Finset.sum_const_nat (fun _ _ => rfl), mul_comm]
  have hlt : d * S.card < ∑ v ∈ S, (S.filter (H.Adj v)).card := by
    rw [← hsum]
    exact Finset.sum_lt_sum_of_nonempty hS hcon
  exact absurd (havg S hS) (not_le.mpr hlt)

/-- Lee's theorem [Le17] (SOLVED; not proved here): $R(H)\le2^{2^{O(d)}}n$ for every
$d$-degenerate graph $H$ on $n$ vertices. -/
theorem erdos_problem_163.variants.lee :
    ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ, 1 ≤ d →
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d →
      (ramseyDiag H : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (c * d)) * (n : ℝ) :=
  sorry

/-- Lee's refined bound [Le17] (SOLVED; not proved here): $R(H)\le2^{d\,2^{O(\chi(H))}}n$, stated
for $d$-degenerate $H$ that are $k$-colourable. -/
theorem erdos_problem_163.variants.lee_chromatic :
    ∃ c : ℝ, 0 < c ∧
    ∀ d k : ℕ, 1 ≤ d → 1 ≤ k →
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d → H.Colorable k →
      (ramseyDiag H : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) * (2 : ℝ) ^ (c * k)) * (n : ℝ) :=
  sorry

/-- The conjecture recorded on the page (OPEN): $R(H)\le2^{O(d)}n$ for $d$-degenerate $H$. -/
theorem erdos_problem_163.variants.single_exponential :
    ∃ c : ℝ, 0 < c ∧
    ∀ d : ℕ, 1 ≤ d →
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
    IsDDegenerate H d →
      (ramseyDiag H : ℝ) ≤ (2 : ℝ) ^ (c * d) * (n : ℝ) :=
  sorry

/-- The page's equivalent form with forests (SOLVED, by Lee's theorem; not proved here): if `H` is
the union of `c` forests, then $R(H)\ll_c n$. (A union of $c$ forests is $(2c-1)$-degenerate.) -/
theorem erdos_problem_163.variants.forests :
    ∀ c : ℕ, 1 ≤ c →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (F : Fin c → SimpleGraph (Fin n)),
    (∀ i, (F i).IsAcyclic) → H = ⨆ i, F i →
      (ramseyDiag H : ℝ) ≤ C * (n : ℝ) :=
  sorry

end
