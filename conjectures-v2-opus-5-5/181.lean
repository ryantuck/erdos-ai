-- [AI - Claude Opus 5.5]: Erdős Problem 181 — second-pass formalization
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #181

*Source:* [erdosproblems.com/181](https://www.erdosproblems.com/181) (status **OPEN** at capture:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-20). [BuEr75]
[Er93, p.346]

Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices and $n2^{n-1}$
edges). Prove that $R(Q_n) \ll 2^n$.

Remarks recorded on the page (abridged): conjectured by Burr and Erdős, although in [Er93] Erdős
says the behaviour of $R(Q_n)$ was considered by himself and Sós, who could not decide whether
$R(Q_n)/2^n\to\infty$ or not. The trivial bound is $R(Q_n)\le R(K_{2^n})\le C^{2^n}$ for some
constant $C>1$. This was improved a number of times; the best bound at capture is Tikhomirov's
[Ti22], $R(Q_n)\ll 2^{(2-c)n}$ for some small constant $c>0$ ($c\approx0.03656$ is permissible).
This is #20 in Ramsey Theory in the graphs problem collection.

## Status after capture

Upstream `formal-conjectures` (`2befc3a`) records the problem as **solved**, citing [OpenAI26],
with a linked Lean proof. The metadata mirror (`c443d8c`) still lists it as open. Neither the
preprint nor the Lean proof was read in this review; the statement below is the direction
upstream records as proved.

## Encoding notes

* `ramseyDiag181 H` is the `sInf` of the set of `N` such that every graph on `Fin N` or its
  complement contains a copy of `H`. For finite `H` the set is nonempty (the Erdős–Szekeres bound,
  `ramsey_finset`, PROVED in Lean), so the definition is the diagonal Ramsey number and not the junk
  value `0`. It satisfies `2^n ≤ R(Q_n) ≤ 4^(2^n)` (`variants.lower_bound`, `variants.trivial_bound`,
  both PROVED); the upper bound is the page's trivial bound with `C = 4`.
* The restriction `1 ≤ n` is harmless: `R(Q_0) = 1`, and the lower bound forces `C ≥ 1` anyway.
* `hypercubeGraph` adjacency is Hamming distance one (`hypercubeGraph_adj_iff`), and
  `containsCopy181 G H` is Mathlib's `H ⊑ G` (`containsCopy181_iff`); both PROVED.
* The Erdős–Sós question has the answer no once the main theorem holds
  (`variants.not_tendsto_of_main`, PROVED).

## References

From the site's `/latex/181` bibliography:
* [Er93] Erdős, Paul, _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Math. (1993), 333–350.
* [Ti22] Tikhomirov, K., _A remark on the Ramsey number of the hypercube_. arXiv:2208.14568
  (2022).

Other sources:
* [BuEr75] Burr, S. A. and Erdős, P., the source of the conjecture. **DEFERRED:** no site
  bibliography entry was recovered. The archived DeepMind styled copy gives _On the magnitude of
  generalized Ramsey numbers for graphs_, Infinite and finite sets, Vol. 1 (1975), 214–240;
  upstream's Problem 163 file gives a different title, _On the Ramsey number of graphs with small
  degree-ratio_, Colloq. Math. Soc. János Bolyai (1975).
* [OpenAI26] OpenAI, _The hypercube Ramsey number has linear order_. OpenAI Math Release preprint
  (September 2026). (From upstream's Problem 181 file; not read.)

*Provenance:* second pass of `conjectures/181.lean` (Opus 5.5 review, `opus-5-5-review/181.md`).
-/

/-- The n-dimensional hypercube graph Q_n: vertices are functions Fin n → Bool,
    and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := ⟨fun v ⟨hne, _⟩ => hne rfl⟩

/-- An injective graph homomorphism from H to G: G contains a (not necessarily
    induced) copy of H as a subgraph. -/
def containsCopy181 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The diagonal Ramsey number R(H): the minimum N such that for every simple
    graph G on Fin N, either G or Gᶜ contains a copy of H. -/
noncomputable def ramseyDiag181 {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsCopy181 G H ∨ containsCopy181 Gᶜ H}

/--
Erdős Conjecture (Problem #181) [BuEr75]:

Let Q_n be the n-dimensional hypercube graph. Prove that
  R(Q_n) ≪ 2^n,
i.e., there exists a constant C > 0 such that R(Q_n) ≤ C · 2^n for all n ≥ 1.

(Status: OPEN at capture; upstream records it as solved by [OpenAI26], unverified here.)
-/
theorem erdos_problem_181 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag181 (hypercubeGraph n) : ℝ) ≤ C * (2 ^ n : ℝ) :=
  sorry

/-- Adjacency in `hypercubeGraph n` is Mathlib's Hamming distance one; the `u ≠ v` conjunct is
implied by the cardinality condition (PROVED in Lean). -/
theorem erdos_problem_181.hypercubeGraph_adj_iff {n : ℕ} (u v : Fin n → Bool) :
    (hypercubeGraph n).Adj u v ↔ hammingDist u v = 1 := by
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    refine ⟨fun huv => ?_, h⟩
    rw [huv, hammingDist_self] at h
    exact absurd h (by norm_num)

/-- `containsCopy181 G H` is Mathlib's `H ⊑ G` (PROVED in Lean). -/
theorem erdos_problem_181.containsCopy181_iff {V U : Type*} (G : SimpleGraph V)
    (H : SimpleGraph U) : containsCopy181 G H ↔ H ⊑ G := by
  constructor
  · rintro ⟨f, hf, hadj⟩
    exact ⟨⟨⟨f, fun {u v} h => hadj u v h⟩, hf⟩⟩
  · rintro ⟨c⟩
    exact ⟨c.toHom, c.injective, fun u v h => c.toHom.map_rel h⟩

/-- The Erdős–Szekeres bound (PROVED in Lean): in any graph, a vertex set of size at least
$\binom{s+t}{s}$ contains an `s`-clique or an independent `t`-set. This is the finite Ramsey
theorem behind the page's trivial bound. -/
theorem erdos_problem_181.ramsey_finset {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    ∀ n s t : ℕ, s + t = n → ∀ X : Finset V, (s + t).choose s ≤ X.card →
      (∃ K ⊆ X, K.card = s ∧ G.IsClique (K : Set V)) ∨
      (∃ I ⊆ X, I.card = t ∧ Gᶜ.IsClique (I : Set V)) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s t hst X hX
    rcases s with _ | s
    · exact Or.inl ⟨∅, Finset.empty_subset _, rfl, by simp⟩
    rcases t with _ | t
    · exact Or.inr ⟨∅, Finset.empty_subset _, rfl, by simp⟩
    have hpascal : (s + 1 + (t + 1)).choose (s + 1) =
        (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := by
      have h1 : s + 1 + (t + 1) = (s + (t + 1)) + 1 := by omega
      have h2 : s + 1 + t = s + (t + 1) := by omega
      rw [h1, Nat.choose_succ_succ', h2]
    have hpos : 0 < X.card := lt_of_lt_of_le (Nat.choose_pos (by omega)) hX
    rw [hpascal] at hX
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    set N := (X.erase v).filter (fun w => G.Adj v w) with hNdef
    set M := (X.erase v).filter (fun w => ¬ G.Adj v w) with hMdef
    have hNM : N.card + M.card = X.card - 1 := by
      rw [hNdef, hMdef, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
    have hNX : N ⊆ X := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hMX : M ⊆ X := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
    have hvN : v ∉ N := fun h => by simp [hNdef] at h
    have hvM : v ∉ M := fun h => by simp [hMdef] at h
    by_cases hN : (s + (t + 1)).choose s ≤ N.card
    · rcases ih (s + (t + 1)) (by omega) s (t + 1) rfl N hN with
        ⟨K, hK, hKc, hKcl⟩ | ⟨I, hI, hIc, hIcl⟩
      · refine Or.inl ⟨insert v K, Finset.insert_subset hv (hK.trans hNX), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (fun h => hvN (hK h)), hKc]
        · rw [Finset.coe_insert, isClique_insert]
          refine ⟨hKcl, fun b hb _ => ?_⟩
          have hbN := hK (Finset.mem_coe.1 hb)
          simp only [hNdef, Finset.mem_filter] at hbN
          exact hbN.2
      · exact Or.inr ⟨I, hI.trans hNX, hIc, hIcl⟩
    · have hM : (s + 1 + t).choose (s + 1) ≤ M.card := by omega
      rcases ih (s + 1 + t) (by omega) (s + 1) t rfl M hM with
        ⟨K, hK, hKc, hKcl⟩ | ⟨I, hI, hIc, hIcl⟩
      · exact Or.inl ⟨K, hK.trans hMX, hKc, hKcl⟩
      · refine Or.inr ⟨insert v I, Finset.insert_subset hv (hI.trans hMX), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (fun h => hvM (hI h)), hIc]
        · rw [Finset.coe_insert, isClique_insert]
          refine ⟨hIcl, fun b hb hvb => ?_⟩
          have hbM := hI (Finset.mem_coe.1 hb)
          simp only [hMdef, Finset.mem_filter] at hbM
          exact (compl_adj G v b).2 ⟨hvb, hbM.2⟩

/-- A clique with as many vertices as `H` contains a copy of `H` (PROVED in Lean). -/
theorem erdos_problem_181.containsCopy181_of_isClique {N : ℕ} {U : Type*} [Fintype U]
    (G : SimpleGraph (Fin N)) (H : SimpleGraph U) {K : Finset (Fin N)}
    (hK : K.card = Fintype.card U) (hcl : G.IsClique (K : Set (Fin N))) :
    containsCopy181 G H := by
  let e : U ≃ K := Fintype.equivOfCardEq (by simp [hK])
  refine ⟨fun u => (e u : Fin N), Subtype.val_injective.comp e.injective, fun u v huv => ?_⟩
  exact hcl (Finset.mem_coe.2 (e u).2) (Finset.mem_coe.2 (e v).2)
    (fun h => H.ne_of_adj huv (e.injective (Subtype.val_injective h)))

/-- For finite `H` on `m` vertices, $N=\binom{2m}{m}$ lies in the set defining `ramseyDiag181`,
which is therefore nonempty (PROVED in Lean). -/
theorem erdos_problem_181.forces_choose {U : Type*} [Fintype U] (H : SimpleGraph U)
    (G : SimpleGraph (Fin ((2 * Fintype.card U).choose (Fintype.card U)))) :
    containsCopy181 G H ∨ containsCopy181 Gᶜ H := by
  rcases erdos_problem_181.ramsey_finset G _ (Fintype.card U) (Fintype.card U) rfl
      Finset.univ (by rw [Finset.card_univ, Fintype.card_fin, two_mul]) with
    ⟨K, -, hK, hcl⟩ | ⟨I, -, hI, hcl⟩
  · exact Or.inl (erdos_problem_181.containsCopy181_of_isClique G H hK hcl)
  · exact Or.inr (erdos_problem_181.containsCopy181_of_isClique Gᶜ H hI hcl)

/-- For finite `H` on `m` vertices, $m\le R(H)\le\binom{2m}{m}$ (PROVED in Lean). -/
theorem erdos_problem_181.ramseyDiag181_bounds {U : Type*} [Fintype U] (H : SimpleGraph U) :
    Fintype.card U ≤ ramseyDiag181 H ∧
      ramseyDiag181 H ≤ (2 * Fintype.card U).choose (Fintype.card U) := by
  unfold ramseyDiag181
  refine ⟨le_csInf ⟨_, erdos_problem_181.forces_choose H⟩ fun N hN => ?_,
    Nat.sInf_le (erdos_problem_181.forces_choose H)⟩
  rcases hN ⊥ with ⟨f, hf, -⟩ | ⟨f, hf, -⟩ <;> simpa using Fintype.card_le_of_injective f hf

/-- The page's trivial bound $R(Q_n)\le R(K_{2^n})\le C^{2^n}$, with $C=4$ (PROVED in Lean). -/
theorem erdos_problem_181.variants.trivial_bound (n : ℕ) :
    ramseyDiag181 (hypercubeGraph n) ≤ 4 ^ 2 ^ n := by
  refine (erdos_problem_181.ramseyDiag181_bounds (hypercubeGraph n)).2.trans ?_
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  calc (2 * 2 ^ n).choose (2 ^ n) ≤ 2 ^ (2 * 2 ^ n) := Nat.choose_le_two_pow _ _
    _ = 4 ^ 2 ^ n := by rw [pow_mul]; norm_num

/-- The trivial lower bound $2^n\le R(Q_n)$: a copy of $Q_n$ needs $2^n$ vertices (PROVED in
Lean). In particular any constant `C` in the main theorem is at least `1`. -/
theorem erdos_problem_181.variants.lower_bound (n : ℕ) :
    2 ^ n ≤ ramseyDiag181 (hypercubeGraph n) := by
  simpa using (erdos_problem_181.ramseyDiag181_bounds (hypercubeGraph n)).1

/-- Tikhomirov's bound [Ti22] (SOLVED; not proved here): $R(Q_n)\ll2^{(2-c)n}$ for some
constant $c>0$; the page notes that $c\approx0.03656$ is permissible. -/
theorem erdos_problem_181.variants.tikhomirov :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag181 (hypercubeGraph n) : ℝ) ≤ C * (2 : ℝ) ^ ((2 - c) * (n : ℝ)) :=
  sorry

/-- The Erdős–Sós question, whether $R(Q_n)/2^n\to\infty$, has the answer no once the main
theorem holds (PROVED in Lean: the main statement implies the ratio does not tend to infinity). -/
theorem erdos_problem_181.variants.not_tendsto_of_main
    (h : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (ramseyDiag181 (hypercubeGraph n) : ℝ) ≤ C * (2 ^ n : ℝ)) :
    ¬ Filter.Tendsto (fun n : ℕ => (ramseyDiag181 (hypercubeGraph n) : ℝ) / 2 ^ n)
      Filter.atTop Filter.atTop := by
  obtain ⟨C, -, hC⟩ := h
  intro ht
  obtain ⟨n, hn1, hn2⟩ :=
    ((ht.eventually_ge_atTop (C + 1)).and (Filter.eventually_ge_atTop 1)).exists
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hle := hC n hn2
  rw [le_div_iff₀ h2] at hn1
  nlinarith

end
