-- [AI - Claude Opus 5.5]: Erdős Problem 171 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

import Mathlib.Combinatorics.HalesJewett

/-!
# Erdős Problem #171 (the density Hales–Jewett theorem)

*Source:* [erdosproblems.com/171](https://www.erdosproblems.com/171) (status **PROVED**: "This has
been solved in the affirmative."; captured 2026-02-20; page edited 25 January 2026; OEIS A156989).
[ErGr79] [ErGr80]

Is it true that for every $\epsilon>0$ and integer $t\geq 1$, if $N$ is sufficiently large and $A$
is a subset of $[t]^N$ of size at least $\epsilon t^N$ then $A$ must contain a combinatorial line
$P$ (a set $P=\{p_1,\ldots,p_t\}$ where for each coordinate $1\leq j\leq t$ the $j$th coordinate
of $p_i$ is either $i$ or constant).

Remarks recorded on the page: the 'density Hales-Jewett' problem. This was proved by Furstenberg
and Katznelson [FuKa91]. A new elementary proof, which gives quantitative bounds, was proved by the
Polymath project [Po12].

After the capture, the mirror (`b916d95`) records `proved (Lean)` (2026-08-24), and upstream
`formal-conjectures` (`df3f12d`) links a Lean proof of its version of the statement. Neither proof
was examined here.

## Encoding notes

* The question is a yes/no question whose answer is yes; the input asserts the statement directly.
* `[t]` is `Fin t` and `[t]^N` is `Fin N → Fin t`. (The page's "each coordinate $1\le j\le t$" is a
  slip for $1\le j\le N$.)
* `IsCombLine t N P` is Mathlib's notion: for `1 ≤ t`, `P` is a combinatorial line exactly when it is
  `fun i => l i` for some `l : Combinatorics.Line (Fin t) (Fin N)` (`isCombLine_iff`, PROVED). So
  the main theorem is equivalent to upstream's form with Mathlib lines (`variants.main_iff_line`,
  PROVED).
* The edge case `t = 1` holds (`variants.t_one`, PROVED): a nonempty `A ⊆ [1]^N` contains the
  single point, which is a line once `N ≥ 1`.

## References

From the site's `/latex/171` bibliography:
* [FuKa91] Furstenberg, H. and Katznelson, Y., _A density version of the Hales-Jewett Theorem_. J.
  Analyse Math. (1991), 64–119.
* [Po12] Polymath, D. H. J., _A new proof of the density Hales–Jewett theorem_. Ann. of Math. (2)
  (2012), 1283–1327.

Erdős's sources:
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring; no site entry was recovered, and the archived DeepMind
  copy gives a different subtitle.)

*Provenance:* second pass of `conjectures/171.lean` (Opus 5.5 review, `opus-5-5-review/171.md`).
-/

/-- A combinatorial line in [t]^N is a family of t points parametrized by Fin t,
    determined by a non-empty set S of "active" coordinates and fixed values c
    for inactive coordinates. The i-th point has coordinate j equal to i if j is
    active, and equal to c j if j is inactive. -/
def IsCombLine (t N : ℕ) (P : Fin t → (Fin N → Fin t)) : Prop :=
  ∃ (S : Finset (Fin N)) (c : Fin N → Fin t),
    S.Nonempty ∧
    ∀ (i : Fin t) (j : Fin N),
      P i j = if j ∈ S then i else c j

/--
Erdős Problem #171 (Density Hales-Jewett theorem) [ErGr79, ErGr80]:

For every ε > 0 and integer t ≥ 1, there exists N₀ such that for all N ≥ N₀,
every subset A of [t]^N with |A| ≥ ε · t^N contains a combinatorial line.
(Status: PROVED [FuKa91]; the statement is the true direction.)
-/
theorem erdos_problem_171 :
    ∀ (t : ℕ), 1 ≤ t →
    ∀ (ε : ℝ), 0 < ε →
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset (Fin N → Fin t)),
    (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
    ∃ (P : Fin t → (Fin N → Fin t)),
      IsCombLine t N P ∧ ∀ (i : Fin t), P i ∈ A :=
  sorry

/-- For `1 ≤ t`, `IsCombLine` is Mathlib's `Combinatorics.Line`: `P` is a combinatorial line exactly
when `P = fun i => l i` for a line `l` (PROVED in Lean). -/
theorem erdos_problem_171.isCombLine_iff {t N : ℕ} (ht : 1 ≤ t) (P : Fin t → (Fin N → Fin t)) :
    IsCombLine t N P ↔ ∃ l : Combinatorics.Line (Fin t) (Fin N), ∀ i, P i = l i := by
  classical
  constructor
  · rintro ⟨S, c, ⟨j₀, hj₀⟩, hP⟩
    refine ⟨⟨fun j => if j ∈ S then none else some (c j), j₀, by simp [hj₀]⟩, fun i => ?_⟩
    funext j
    rw [hP i j, Combinatorics.Line.coe_apply]
    split_ifs with h <;> simp [h]
  · rintro ⟨l, hl⟩
    obtain ⟨j₀, hj₀⟩ := l.proper
    refine ⟨Finset.univ.filter (fun j => l.idxFun j = none),
      fun j => (l.idxFun j).getD ⟨0, ht⟩, ⟨j₀, by simp [hj₀]⟩, fun i j => ?_⟩
    rw [hl i, Combinatorics.Line.coe_apply]
    by_cases h : l.idxFun j = none
    · simp [h]
    · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp h
      simp [← hy]

/-- The main theorem is equivalent to the same statement with Mathlib's combinatorial lines, the
form upstream uses (PROVED in Lean). -/
theorem erdos_problem_171.variants.main_iff_line :
    (∀ (t : ℕ), 1 ≤ t →
      ∀ (ε : ℝ), 0 < ε →
      ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
      ∀ (A : Finset (Fin N → Fin t)),
      (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
      ∃ (P : Fin t → (Fin N → Fin t)),
        IsCombLine t N P ∧ ∀ (i : Fin t), P i ∈ A) ↔
    (∀ (t : ℕ), 1 ≤ t →
      ∀ (ε : ℝ), 0 < ε →
      ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
      ∀ (A : Finset (Fin N → Fin t)),
      (A.card : ℝ) ≥ ε * (t : ℝ) ^ N →
      ∃ l : Combinatorics.Line (Fin t) (Fin N), ∀ i : Fin t, l i ∈ A) := by
  constructor
  · intro h t ht ε hε
    obtain ⟨N₀, hN₀⟩ := h t ht ε hε
    refine ⟨N₀, fun N hN A hA => ?_⟩
    obtain ⟨P, hP, hPA⟩ := hN₀ N hN A hA
    obtain ⟨l, hl⟩ := (erdos_problem_171.isCombLine_iff ht P).mp hP
    exact ⟨l, fun i => hl i ▸ hPA i⟩
  · intro h t ht ε hε
    obtain ⟨N₀, hN₀⟩ := h t ht ε hε
    refine ⟨N₀, fun N hN A hA => ?_⟩
    obtain ⟨l, hl⟩ := hN₀ N hN A hA
    exact ⟨fun i => l i, (erdos_problem_171.isCombLine_iff ht _).mpr ⟨l, fun i => rfl⟩, hl⟩

/-- The case `t = 1` (PROVED in Lean): a nonempty subset of the one-point cube `[1]^N`, `N ≥ 1`,
contains the one-point line. -/
theorem erdos_problem_171.variants.t_one :
    ∀ (ε : ℝ), 0 < ε →
    ∃ (N₀ : ℕ), ∀ (N : ℕ), N₀ ≤ N →
    ∀ (A : Finset (Fin N → Fin 1)),
    (A.card : ℝ) ≥ ε * ((1 : ℕ) : ℝ) ^ N →
    ∃ (P : Fin 1 → (Fin N → Fin 1)),
      IsCombLine 1 N P ∧ ∀ (i : Fin 1), P i ∈ A := by
  intro ε hε
  refine ⟨1, fun N hN A hA => ?_⟩
  have hpos : 0 < A.card := by
    have : (0 : ℝ) < A.card := by
      calc (0 : ℝ) < ε * ((1 : ℕ) : ℝ) ^ N := by simp [hε]
        _ ≤ A.card := hA
    exact_mod_cast this
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  refine ⟨fun _ => p, ⟨Finset.univ, fun _ => 0, ⟨⟨0, hN⟩, Finset.mem_univ _⟩, ?_⟩, fun _ => hp⟩
  intro i j
  simp only [Finset.mem_univ, if_true]
  exact Subsingleton.elim _ _
