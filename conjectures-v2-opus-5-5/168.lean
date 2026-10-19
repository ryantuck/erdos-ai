-- [AI - Claude Opus 5.5]: Erdős Problem 168 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup


/-!
# Erdős Problem #168

*Source:* [erdosproblems.com/168](https://www.erdosproblems.com/168) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-03-05; page edited 24 October 2025;
OEIS A004059, A057561, A094708, A386439). [ErGr79] [ErGr80]

Let $F(N)$ be the size of the largest subset of $\{1,\ldots,N\}$ which does not contain any set of
the form $\{n,2n,3n\}$. What is $\lim_{N\to\infty}\frac{F(N)}{N}$? Is this limit irrational?

Remarks recorded on the page: this limit was proved to exist by Graham, Spencer and Witsenhausen
[GSW77], who showed it is equal to $\frac13\sum_{k\in K}\frac1{d_k}$, where $d_1<d_2<\cdots$ are the
$3$-smooth numbers and $K$ is the set of $k$ for which $f(k)>f(k-1)$, where $f$ counts the largest
subset of $\{d_1,\ldots,d_k\}$ that avoids $\{n,2n,3n\}$. Similar questions can be asked for the
density or upper density of infinite sets without such configurations. The limit can be estimated
by elementary arguments. Eberhard has used the formula of [GSW77] to calculate the value of the
limit as $0.800965\cdots$.

## Encoding notes

* `erdos168_F N` is the maximum of `S.card` over subsets `S ⊆ {1, …, N}` with no `n ∈ S` such that
  `2n, 3n ∈ S`. Checked values (PROVED by `decide`): `F 0, F 1, F 2, F 3 = 0, 1, 2, 2` and
  `F 6 = 5`; `F N ≤ N` and every admissible `S` has `S.card ≤ F N` (PROVED).
* The page asks two questions. The main theorem encodes the second ("is the limit irrational?") in
  its "yes" direction: the limit exists and is irrational. Since the limit exists [GSW77]
  (`variants.limit_exists`), this is the same as "the limit is irrational" (`variants.main_iff`,
  PROVED in Lean).
* The first question ("what is the limit?") asks for a value; no closed form is conjectured, so it
  has no formal target here. The value is recorded as `variants.limit_approx`.

## References

* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [ErGr79], [GSW77]: **DEFERRED**; no site entry was recovered.

*Provenance:* second pass of `conjectures/168.lean` (Opus 5.5 review, `opus-5-5-review/168.md`).
-/

open Finset Filter

noncomputable section

/--
F(N) is the size of the largest subset of {1,…,N} that contains no
three-term set of the form {n, 2n, 3n}.
-/
def erdos168_F (N : ℕ) : ℕ :=
  Finset.sup (Finset.Icc 1 N).powerset (fun S =>
    if ∀ n ∈ S, ¬(2 * n ∈ S ∧ 3 * n ∈ S) then S.card else 0)

/--
Erdős Problem #168 [ErGr79, ErGr80]:

Let F(N) be the size of the largest subset of {1,…,N} which does not
contain any set of the form {n, 2n, 3n}. Graham, Spencer, and
Witsenhausen [GSW77] proved that the limit lim_{N→∞} F(N)/N exists and
equals approximately 0.800965…

Is this limit irrational?

(Status: OPEN. Review note: [GSW77] proved that the limit exists and gave a formula for it; the
value 0.800965… was computed by Eberhard from that formula.)
-/
theorem erdos_problem_168 :
    ∃ α : ℝ,
      Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds α) ∧
      Irrational α :=
  sorry


/-- Small values (PROVED by `decide`): `F 0 = 0`, `F 1 = 1`, `F 2 = 2`, `F 3 = 2`. -/
theorem erdos_problem_168.F_small :
    erdos168_F 0 = 0 ∧ erdos168_F 1 = 1 ∧ erdos168_F 2 = 2 ∧ erdos168_F 3 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `F 6 = 5` (PROVED by kernel `decide`): `{1, 3, 4, 5, 6}` works, and no `6`-element set does,
since `{1, 2, 3}` must be avoided. -/
theorem erdos_problem_168.F_six : erdos168_F 6 = 5 := by decide +kernel

/-- `F N ≤ N` (PROVED in Lean). -/
theorem erdos_problem_168.F_le (N : ℕ) : erdos168_F N ≤ N := by
  unfold erdos168_F
  apply Finset.sup_le
  intro S hS
  rw [Finset.mem_powerset] at hS
  split_ifs
  · calc S.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hS
      _ = N := by simp
  · exact Nat.zero_le _

/-- Every subset of `{1, …, N}` without `{n, 2n, 3n}` has at most `F N` elements (PROVED in Lean). -/
theorem erdos_problem_168.card_le_F (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 N)
    (h : ∀ n ∈ S, ¬(2 * n ∈ S ∧ 3 * n ∈ S)) : S.card ≤ erdos168_F N := by
  unfold erdos168_F
  have := Finset.le_sup (f := fun S : Finset ℕ =>
    if ∀ n ∈ S, ¬(2 * n ∈ S ∧ 3 * n ∈ S) then S.card else 0) (Finset.mem_powerset.mpr hS)
  dsimp only at this
  rwa [if_pos h] at this

/-- Graham, Spencer and Witsenhausen [GSW77] (SOLVED; not proved here): the limit exists. -/
theorem erdos_problem_168.variants.limit_exists :
    ∃ L : ℝ, Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds L) :=
  sorry

/-- Given the limit `L`, the main theorem says exactly that `L` is irrational (PROVED in Lean). -/
theorem erdos_problem_168.variants.main_iff {L : ℝ}
    (hL : Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds L)) :
    (∃ α : ℝ,
      Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds α) ∧
      Irrational α) ↔ Irrational L := by
  constructor
  · rintro ⟨α, hα, hirr⟩
    rwa [tendsto_nhds_unique hα hL] at hirr
  · intro h
    exact ⟨L, hL, h⟩

/-- The value (SOLVED from the [GSW77] formula: Eberhard's computation $0.800965\ldots$, and the
review's computation, which places the limit in $[0.8009644, 0.8009664]$; not proved here). -/
theorem erdos_problem_168.variants.limit_approx :
    ∃ L : ℝ, Tendsto (fun N => (erdos168_F N : ℝ) / (N : ℝ)) atTop (nhds L) ∧
      (0.80096 : ℝ) < L ∧ L < 0.80097 :=
  sorry

end
