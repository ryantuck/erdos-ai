-- [AI - Claude Sonnet 5.5]: Erdős Problem 160 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Lattice

open Finset

open Filter

/-!
# Erdős Problem #160: Colouring $\{1,\ldots,N\}$ so that every 4-term progression has three colours

*Source:* [erdosproblems.com/160](https://www.erdosproblems.com/160) (banner **OPEN**: "This is open, and cannot be
resolved with a finite computation."; page last edited 02 December 2025; captured 2026-03-05 as the page and as the tidied
problem box, with identical content; "Formalised statement? Yes", the OEIS field "Possible", 1 comment, not captured).
[Er89]

Let $h(N)$ be the smallest $k$ such that $\{1,\ldots,N\}$ can be coloured with $k$ colours so that every four-term
arithmetic progression must contain at least three distinct colours. Estimate $h(N)$.

Remarks recorded on the page: Investigated by Erdős and Freud. This has been discussed on MathOverflow, where LeechLattice
shows $h(N)\ll N^{2/3}$. In the comments of this site Hunter improves this to
$h(N)\ll N^{\frac{\log 3}{\log 22}+o(1)}$ (note $\frac{\log 3}{\log 22}\approx 0.355$). The observation of Zach Hunter in
that question coupled with recent progress on the size of subsets without three-term arithmetic progression (see [BlSi23]
which improves slightly on the bounds due to Kelley and Meka [KeMe23]) imply that $h(N)\gg \exp(c(\log N)^{1/9})$ for some
$c>0$.

Tags: additive combinatorics, arithmetic progressions.

**Status.** OPEN: the order of magnitude of $h(N)$ is not known; the page records the gap
$\exp(c(\log N)^{1/9})\ll h(N)\ll N^{\log 3/\log 22+o(1)}$. The mirror (`teorth/erdosproblems`, `b916d95`) has `open` since
2025-08-31, no prize, formalised `yes`. Upstream's `160.lean` (`df3f12d`) defines `h` and has the two bounds of the remarks
as `research solved` and two estimation requests as `research open` with `answer(sorry)`.

**What the first pass formalized.** The first pass stated only `∀ k, ∃ N₀, ∀ N ≥ N₀, ¬ AdmitsRainbow4AP N k`, that is,
$h(N)\to\infty$. That is not the page's request, and it is not open: it is a corollary of van der Waerden's theorem (a
$k$-colouring of $\{1,\ldots,N\}$ has a monochromatic 4-term progression once $N$ is large, and a monochromatic
progression has one colour). `variants.first_pass` proves it in Lean from Mathlib's Hales–Jewett theorem, with
$N_0=3m+1$ for $m$ the dimension that theorem provides, and `variants.minRainbowColours_tendsto` states it as
"`h N → ∞`". The page's lower bound is far stronger. v2 therefore makes the page's request the main theorem.

**Encoding.**
* `RainbowOn4AP N k f` says that the colouring `f : ℕ → Fin k` has at least three distinct colours on every 4-term
  progression `a, a + d, a + 2d, a + 3d` inside `{1, …, N}` (`a ≥ 1`, `d ≥ 1`). Only the values of `f` on `{1, …, N}` matter.
  `AdmitsRainbow4AP N k` says that such a colouring exists.
* `minRainbowColours N` is the page's `h(N)`: the least `k` with `AdmitsRainbow4AP N k`. The set is nonempty
  (`admits_self`: `N + 1` colours suffice), so this is a true minimum. `variants.minRainbowColours_one` and `_four` evaluate
  it: `h 1 = 1` and `h 4 = 3` (two colours never give three on a progression). A search outside Lean gives the values
  in the review.
* The page's request "Estimate $h(N)$" is read here, as in `142.lean` and `148.lean`, as the order of magnitude of `h`:
  there is a closed-form function `f` (built from constants and the identity by sums, products, reciprocals, `exp` and `log`,
  the class `IsExpLog`) and constants `c, C > 0` with `c f(N) ≤ h(N) ≤ C f(N)` for all large `N`. The class of closed forms is
  an editorial choice, and the statement is OPEN.
* `variants.upper_hunter`, `variants.upper_leechlattice` and `variants.lower_bloom_sisask` record the page's bounds, with
  `sorry`. They are known results (from an answer on MathOverflow, a comment on the site, and [BlSi23], [KeMe23]) and are
  not proved here. **DEFERRED:** none of them was seen. Upstream's lower bound has the exponent `1/12` (from [KeMe23] alone);
  the page's is `1/9` (with [BlSi23]).

## References

* [Er89] The page's key. **DEFERRED:** no bibliography entry for it was recovered (there is no `/latex/160` fetch and no
  other fetch that defines it).
* [KeMe23] Kelley, Z. and Meka, R., _Strong Bounds for 3-Progressions_. arXiv:2302.05537 (2023). (From the `/latex/721`
  fetch in the session logs.)
* [BlSi23] Bloom, T. F. and Sisask, O., _An improvement to the Kelley–Meka bounds on three-term arithmetic progressions_.
  arXiv:2309.02353 (2023). (From the `/latex/721` fetch.)
* The MathOverflow question and answer of LeechLattice, and Hunter's observation, are cited by the page as web
  discussions, not as publications.
-/

/--
A coloring `f : ℕ → Fin k` is **rainbow on 4-APs** in `{1,…,N}` if every
four-term arithmetic progression `{a, a+d, a+2d, a+3d} ⊆ {1,…,N}` uses at
least three distinct colours.
-/
def RainbowOn4AP (N : ℕ) (k : ℕ) (f : ℕ → Fin k) : Prop :=
  ∀ a d : ℕ, 0 < d → 1 ≤ a → a + 3 * d ≤ N →
    2 < ({f a, f (a + d), f (a + 2 * d), f (a + 3 * d)} : Finset (Fin k)).card

/--
There exists a coloring of `{1,…,N}` with `k` colours that is rainbow on 4-APs.
-/
def AdmitsRainbow4AP (N k : ℕ) : Prop :=
  ∃ f : ℕ → Fin k, RainbowOn4AP N k f

/-- The page's `h(N)`: the smallest `k` such that `{1, …, N}` has a `k`-colouring that is rainbow on 4-APs. -/
noncomputable def minRainbowColours (N : ℕ) : ℕ :=
  sInf {k : ℕ | AdmitsRainbow4AP N k}

/--
The closed forms: functions built from constants and the identity by sums, products, reciprocals,
`exp` and `log`. As in `142.lean` and `148.lean`, an "estimate" is read as an order of magnitude given by such a function.
-/
inductive IsExpLog : (ℝ → ℝ) → Prop
  | const (c : ℝ) : IsExpLog (fun _ => c)
  | id : IsExpLog (fun x => x)
  | add {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x + g x)
  | mul {f g : ℝ → ℝ} : IsExpLog f → IsExpLog g → IsExpLog (fun x => f x * g x)
  | inv {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => (f x)⁻¹)
  | exp {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.exp (f x))
  | log {f : ℝ → ℝ} : IsExpLog f → IsExpLog (fun x => Real.log (f x))

/--
Erdős Problem #160 [Er89] (OPEN):

Let h(N) be the smallest k such that {1,…,N} can be coloured with k colours
so that every four-term arithmetic progression must contain at least three
distinct colours. Estimate h(N).

The page records the gap exp(c (log N)^{1/9}) ≪ h(N) ≪ N^{log 3 / log 22 + o(1)}. The request is read here as the order
of magnitude of h(N): there is a closed-form function f (built from constants and the identity by sums, products,
reciprocals, exp and log) and constants c, C > 0 with c · f(N) ≤ h(N) ≤ C · f(N) for all large N. The class of closed
forms is an editorial choice. The first pass's statement "h(N) → ∞" is `variants.first_pass`, now PROVED.
-/
theorem erdos_problem_160 :
    ∃ f : ℝ → ℝ, IsExpLog f ∧ (∀ᶠ N : ℕ in atTop, 0 < f N) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ N : ℕ in atTop,
        c * f N ≤ (minRainbowColours N : ℝ) ∧ (minRainbowColours N : ℝ) ≤ C * f N :=
  sorry

/--
The first pass's statement (PROVED in Lean; it was marked open there): for every `k` there is `N₀` such that for all
`N ≥ N₀` no `k`-colouring of `{1,…,N}` is rainbow on 4-APs. It follows from the Hales–Jewett theorem in Mathlib, through
van der Waerden's theorem: a `k`-colouring of the cube `(Fin 4)^m`, `m` large, by the colour of `∑ xᵢ + 1` has a monochromatic
combinatorial line, whose four points are a monochromatic 4-term progression of `{1, …, 3m + 1}`.
-/
theorem erdos_problem_160.variants.first_pass :
    ∀ k : ℕ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ¬ AdmitsRainbow4AP N k := by
  intro k
  classical
  obtain ⟨ι, _inst, hι⟩ := Combinatorics.Line.exists_mono_in_high_dimension (Finset.range 4) (Fin k)
  refine ⟨3 * Fintype.card ι + 1, fun N hN hadm => ?_⟩
  obtain ⟨f, hf⟩ := hadm
  obtain ⟨l, c, hl⟩ := hι (fun v => f (∑ i, (v i : ℕ) + 1))
  set s : Finset ι := {i | l.idxFun i = none} with hs
  have hspos : 0 < s.card := Finset.card_pos.mpr ⟨l.proper.choose, by
    rw [hs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  set b : ℕ := ∑ i ∈ sᶜ, ((l.idxFun i).map (fun m : Finset.range 4 => (m : ℕ))).getD 0 with hb
  have hsum : ∀ x (xs : x ∈ Finset.range 4),
      ∑ i, ((l ⟨x, xs⟩ i : Finset.range 4) : ℕ) = s.card * x + b := by
    intro x xs
    rw [← Finset.sum_add_sum_compl s]
    congr 1
    · apply Finset.sum_const_nat
      intro i hi
      rw [hs, Finset.mem_filter] at hi
      rw [Combinatorics.Line.coe_apply, hi.right]
      rfl
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
      obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
      simp [← hy, Option.map_some, Option.getD]
  have hpt : ∀ x (xs : x ∈ Finset.range 4), f (s.card * x + b + 1) = c := by
    intro x xs
    rw [← hl ⟨x, xs⟩, ← hsum x xs]
  have hbound : s.card * 3 + b ≤ 3 * Fintype.card ι := by
    rw [← hsum 3 (by decide)]
    calc ∑ i, ((l ⟨3, by decide⟩ i : Finset.range 4) : ℕ) ≤ ∑ _i : ι, 3 := by
          apply Finset.sum_le_sum
          intro i _
          have := (l ⟨3, by decide⟩ i).2
          simp only [Finset.mem_range] at this
          omega
      _ = 3 * Fintype.card ι := by simp [mul_comm]
  have key := hf (b + 1) s.card hspos (by omega) (by omega)
  have e0 := hpt 0 (by decide)
  have e1 := hpt 1 (by decide)
  have e2 := hpt 2 (by decide)
  have e3 := hpt 3 (by decide)
  have h1 : s.card * 0 + b + 1 = b + 1 := by omega
  have h2 : s.card * 1 + b + 1 = b + 1 + s.card := by omega
  have h3 : s.card * 2 + b + 1 = b + 1 + 2 * s.card := by omega
  have h4 : s.card * 3 + b + 1 = b + 1 + 3 * s.card := by omega
  rw [h1] at e0
  rw [h2] at e1
  rw [h3] at e2
  rw [h4] at e3
  rw [e0, e1, e2, e3] at key
  simp at key

/-- A colouring rainbow on 4-APs with `j` colours gives one with `k ≥ j` colours (PROVED in Lean). -/
theorem erdos_problem_160.admits_mono_k {N j k : ℕ} (hjk : j ≤ k) (h : AdmitsRainbow4AP N j) :
    AdmitsRainbow4AP N k := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun a => Fin.castLE hjk (f a), fun a d hd ha had => ?_⟩
  have := hf a d hd ha had
  have himg : ({Fin.castLE hjk (f a), Fin.castLE hjk (f (a + d)), Fin.castLE hjk (f (a + 2 * d)),
      Fin.castLE hjk (f (a + 3 * d))} : Finset (Fin k)) =
      Finset.image (Fin.castLE hjk) {f a, f (a + d), f (a + 2 * d), f (a + 3 * d)} := by
    simp [Finset.image_insert]
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hjk)]
  exact this

/-- A colouring rainbow on 4-APs in `{1, …, N}` is rainbow in `{1, …, M}` for `M ≤ N` (PROVED in Lean). -/
theorem erdos_problem_160.admits_antitone {M N k : ℕ} (hMN : M ≤ N) (h : AdmitsRainbow4AP N k) :
    AdmitsRainbow4AP M k := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun a d hd ha had => hf a d hd ha (by omega)⟩

/-- `N + 1` colours always suffice, giving every element of `{1, …, N}` its own colour (PROVED in Lean), so
`minRainbowColours N` is a true minimum. -/
theorem erdos_problem_160.admits_self (N : ℕ) : AdmitsRainbow4AP N (N + 1) := by
  refine ⟨fun a => ⟨a % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩, fun a d hd ha had => ?_⟩
  beta_reduce
  have hx : ({(⟨a % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩ : Fin (N + 1)),
      ⟨(a + d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩,
      ⟨(a + 2 * d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩} : Finset (Fin (N + 1))).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · simp only [ne_eq, Fin.mk.injEq]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [ne_eq, Fin.mk.injEq]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [ne_eq, Fin.mk.injEq]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  have hsub : ({(⟨a % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩ : Fin (N + 1)),
      ⟨(a + d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩,
      ⟨(a + 2 * d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩} : Finset (Fin (N + 1))) ⊆
      ({(⟨a % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩ : Fin (N + 1)),
      ⟨(a + d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩,
      ⟨(a + 2 * d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩,
      ⟨(a + 3 * d) % (N + 1), Nat.mod_lt _ (Nat.succ_pos N)⟩} : Finset (Fin (N + 1))) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    tauto
  have := Finset.card_le_card hsub
  omega

/-- The first pass's statement is "`h N → ∞`" (PROVED in Lean): for every `K`, `h N ≥ K` for all large `N`. -/
theorem erdos_problem_160.variants.minRainbowColours_tendsto :
    Tendsto (fun N : ℕ => minRainbowColours N) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  obtain ⟨N₀, hN₀⟩ := erdos_problem_160.variants.first_pass K
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun N hN => ?_⟩
  have hne : {k : ℕ | AdmitsRainbow4AP N k}.Nonempty := ⟨N + 1, erdos_problem_160.admits_self N⟩
  have hmem : AdmitsRainbow4AP N (minRainbowColours N) := Nat.sInf_mem hne
  by_contra hlt
  push_neg at hlt
  exact hN₀ N hN (erdos_problem_160.admits_mono_k (Nat.le_of_lt hlt) hmem)

/-- `h` is nondecreasing (PROVED in Lean). -/
theorem erdos_problem_160.variants.minRainbowColours_mono (N : ℕ) :
    minRainbowColours N ≤ minRainbowColours (N + 1) := by
  have hne : {k : ℕ | AdmitsRainbow4AP (N + 1) k}.Nonempty :=
    ⟨N + 2, erdos_problem_160.admits_self (N + 1)⟩
  have hmem : AdmitsRainbow4AP (N + 1) (minRainbowColours (N + 1)) := Nat.sInf_mem hne
  exact Nat.sInf_le (erdos_problem_160.admits_antitone (Nat.le_succ N) hmem)

/-- `h(1) = 1`: with no 4-term progression one colour suffices, and no colouring has zero colours (PROVED in Lean). -/
theorem erdos_problem_160.variants.minRainbowColours_one : minRainbowColours 1 = 1 := by
  have h1 : AdmitsRainbow4AP 1 1 := ⟨fun _ => 0, fun a d hd ha had => by omega⟩
  have h0 : ¬ AdmitsRainbow4AP 1 0 := fun ⟨f, _⟩ => (f 0).elim0
  have hne1 : {k : ℕ | AdmitsRainbow4AP 1 k}.Nonempty := ⟨1, h1⟩
  have hmem : AdmitsRainbow4AP 1 (minRainbowColours 1) := Nat.sInf_mem hne1
  have hle : minRainbowColours 1 ≤ 1 := Nat.sInf_le h1
  have hne : minRainbowColours 1 ≠ 0 := fun h => h0 (h ▸ hmem)
  omega

/-- `h(4) = 3`: the only 4-term progression in `{1, …, 4}` is `1, 2, 3, 4`; three colours suffice, and two colours never
give three on a progression (PROVED in Lean). -/
theorem erdos_problem_160.variants.minRainbowColours_four : minRainbowColours 4 = 3 := by
  have h3 : AdmitsRainbow4AP 4 3 := by
    refine ⟨fun a => if a = 1 then 0 else if a = 2 then 1 else 2, fun a d hd ha had => ?_⟩
    have : a = 1 ∧ d = 1 := by omega
    obtain ⟨rfl, rfl⟩ := this
    decide
  have h2 : ¬ AdmitsRainbow4AP 4 2 := by
    rintro ⟨f, hf⟩
    have h4 : 2 < ({f 1, f 2, f 3, f 4} : Finset (Fin 2)).card := hf 1 1 (by omega) (by omega) (by omega)
    have hc := Finset.card_le_univ ({f 1, f 2, f 3, f 4} : Finset (Fin 2))
    simp at hc
    omega
  have hne4 : {k : ℕ | AdmitsRainbow4AP 4 k}.Nonempty := ⟨3, h3⟩
  have hmem : AdmitsRainbow4AP 4 (minRainbowColours 4) := Nat.sInf_mem hne4
  have hle : minRainbowColours 4 ≤ 3 := Nat.sInf_le h3
  by_contra hne
  have hlt : minRainbowColours 4 ≤ 2 := by omega
  exact h2 (erdos_problem_160.admits_mono_k hlt hmem)

/-- Hunter's upper bound `h(N) ≪ N^(log 3 / log 22 + o(1))` as the page states it (SOLVED, a comment on the site, not proved
here): for every `ε > 0`, `h(N) ≤ N^(log 3 / log 22 + ε)` for all large `N`. -/
theorem erdos_problem_160.variants.upper_hunter :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (minRainbowColours N : ℝ) ≤ (N : ℝ) ^ (Real.log 3 / Real.log 22 + ε) :=
  sorry

/-- The upper bound `h(N) ≪ N^(2/3)` of LeechLattice (SOLVED, an answer on MathOverflow, not proved here). -/
theorem erdos_problem_160.variants.upper_leechlattice :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (minRainbowColours N : ℝ) ≤ C * (N : ℝ) ^ ((2 : ℝ) / 3) :=
  sorry

/-- The lower bound `h(N) ≫ exp(c (log N)^(1/9))` as the page states it, from Hunter's observation and [BlSi23] (SOLVED,
not proved here): some `c > 0` gives `exp(c (log N)^(1/9)) ≤ h(N)` for all large `N`. -/
theorem erdos_problem_160.variants.lower_bloom_sisask :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      Real.exp (c * (Real.log (N : ℝ)) ^ ((1 : ℝ) / 9)) ≤ (minRainbowColours N : ℝ) :=
  sorry
