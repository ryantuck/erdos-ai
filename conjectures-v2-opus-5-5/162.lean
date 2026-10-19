-- [AI - Claude Opus 5.5]: Erdős Problem 162 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Erdős Problem #162

*Source:* [erdosproblems.com/162](https://www.erdosproblems.com/162) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; no prize; captured 2026-02-20; page edited
30 December 2025). [Er90b, p.21]

Let $\alpha>0$ and $n\geq 1$. Let $F(n,\alpha)$ be the largest $k$ such that there exists some
2-colouring of the edges of $K_n$ in which any induced subgraph $H$ on at least $k$ vertices contains
more than $\alpha\binom{\lvert H\rvert}{2}$ many edges of each colour.

Prove that for every fixed $0\leq \alpha \leq 1/2$, as $n\to\infty$,
$F(n,\alpha)\sim c_\alpha \log n$ for some constant $c_\alpha$.

Remark recorded on the page: it is easy to show with the probabilistic method that there exist
$c_1(\alpha),c_2(\alpha)$ such that $c_1(\alpha)\log n < F(n,\alpha) < c_2(\alpha)\log n$.

## Encoding notes

* **"Largest" is "smallest".** If one colouring works for threshold $k$, it works for every larger
  threshold, so the set of admissible thresholds is upward closed and has no largest element. The
  intended $F(n,\alpha)$ is the least admissible threshold (as in Problem 161), which is what
  `F_erdos162` computes. The set always contains `n + 1`, where the condition is vacuous
  (`erdos_problem_162.mem_succ`), so `F_erdos162 n α ≤ n + 1`.
* **The endpoint $\alpha=1/2$ is degenerate.** The two colour classes of $H$ partition its
  $\binom{\lvert H\rvert}2$ edges, so both cannot exceed half of them. No colouring is
  $\tfrac12$-balanced on a nonempty set, and `F_erdos162 n (1/2) = n + 1` for every `n`
  (`erdos_problem_162.F_half`, PROVED in Lean). So $F(n,1/2)\sim c\log n$ is false, and the first
  pass's statement, which includes $\alpha=1/2$, is false (`variants.first_pass_false`, PROVED). The
  main theorem below takes $0\le\alpha<1/2$.
* **The endpoint $\alpha=0$ is meaningful.** "More than $0$ edges of each colour" means no
  monochromatic set, so $F(n,0)$ is the inverse diagonal Ramsey function:
  $F(n,0)=\min\{m : R(m)>n\}$. Then $F(n,0)\sim c_0\log n$ holds if and only if $R(k)^{1/k}$ converges,
  which is Erdős Problem 77 (open). The main theorem keeps $\alpha=0$, as the page does.
* `F_erdos162` is monotone in `α` (`erdos_problem_162.F_mono`, PROVED).
* "$\sim$" is encoded as: for every $\varepsilon>0$, eventually
  $(c-\varepsilon)\log n\le F(n,\alpha)\le(c+\varepsilon)\log n$, that is $F(n,\alpha)/\log n\to c$,
  with $c>0$.

This is the case $t=2$ of Problem 161 with "more than" in place of "at least". See also Problem 563.

## References

* [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
  differences_. Mathematics of Ramsey theory (1990), 12–28. (From the site's `/latex/161`
  bibliography; no `/latex/162` fetch was recovered.)

*Provenance:* second pass of `conjectures/162.lean` (Opus 5.5 review, `opus-5-5-review/162.md`).
-/

open Finset Real

noncomputable section

/-- A 2-colouring c of the edges (2-element subsets) of Fin n is α-balanced at
    threshold m if for every subset X ⊆ Fin n with |X| ≥ m, each colour class
    contains more than α * C(|X|, 2) many edges within X. -/
def IsEdgeBalanced (n m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card 2 : ℝ) <
        (((X.powersetCard 2).filter (fun S => c S = b)).card : ℝ)

/-- F(n, α) is the smallest threshold m such that there exists a 2-colouring
    of the edges of K_n that is α-balanced at threshold m. (The page says "largest"; the set of
    admissible thresholds is upward closed, so the least one is meant. See the module docstring.) -/
noncomputable def F_erdos162 (n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m α c }

/--
Erdős Problem #162 [Er90b, p.21] (OPEN): for every fixed $0\le\alpha<1/2$,
$F(n,\alpha)\sim c_\alpha\log n$ for some constant $c_\alpha>0$, that is, $F(n,\alpha)/\log n$
converges to a positive limit.

The page says $0\le\alpha\le1/2$; at $\alpha=1/2$ the statement is false, since
$F(n,1/2)=n+1$ (`erdos_problem_162.F_half`), so the endpoint is excluded. The case $\alpha=0$ is the
existence of $\lim R(k)^{1/k}$ (Problem 77). The orders of magnitude are known
(`variants.bounds`); the open content is the existence of the limit constant.
-/
theorem erdos_problem_162 :
    ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          (c - ε) * Real.log (n : ℝ) ≤ (F_erdos162 n α : ℝ) ∧
          (F_erdos162 n α : ℝ) ≤ (c + ε) * Real.log (n : ℝ) :=
  sorry

/-- `n + 1` lies in the set whose `sInf` is `F_erdos162`: no subset of `Fin n` has more than `n`
elements (PROVED in Lean). -/
theorem erdos_problem_162.mem_succ (n : ℕ) (α : ℝ) :
    n + 1 ∈ { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m α c } := by
  refine ⟨fun _ => true, fun X hX _ => ?_⟩
  have h := X.card_le_univ
  simp only [Fintype.card_fin] at h
  omega

/-- `F_erdos162 n α ≤ n + 1` (PROVED in Lean). -/
theorem erdos_problem_162.F_le (n : ℕ) (α : ℝ) : F_erdos162 n α ≤ n + 1 :=
  Nat.sInf_le (erdos_problem_162.mem_succ n α)

/-- `F_erdos162` is monotone in `α` (PROVED in Lean). -/
theorem erdos_problem_162.F_mono (n : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    F_erdos162 n α ≤ F_erdos162 n β := by
  have hne : ({ m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m β c }).Nonempty :=
    ⟨n + 1, erdos_problem_162.mem_succ n β⟩
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨c, fun X hX b => lt_of_le_of_lt ?_ (hc X hX b)⟩
  exact mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)

/-- At `α = 1/2` no colouring is balanced on the whole vertex set (both colour classes cannot
exceed half of the edges), so `F_erdos162 n (1/2) = n + 1` for every `n` (PROVED in Lean). -/
theorem erdos_problem_162.F_half (n : ℕ) : F_erdos162 n (1 / 2) = n + 1 := by
  apply le_antisymm (erdos_problem_162.F_le n _)
  have hne : ({ m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m (1 / 2) c }).Nonempty :=
    ⟨n + 1, erdos_problem_162.mem_succ n _⟩
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  by_contra hlt
  push_neg at hlt
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hle : sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsEdgeBalanced n m (1 / 2) c } ≤
      (Finset.univ : Finset (Fin n)).card := by
    rw [hcard]
    exact Nat.lt_succ_iff.mp hlt
  have h1 := hc Finset.univ hle true
  have h2 := hc Finset.univ hle false
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)).powersetCard 2) (fun S => c S = true)
  simp only [Bool.not_eq_true, Finset.card_powersetCard] at hsum
  have hsumR :
      ((((Finset.univ : Finset (Fin n)).powersetCard 2).filter (fun S => c S = true)).card : ℝ) +
      ((((Finset.univ : Finset (Fin n)).powersetCard 2).filter (fun S => c S = false)).card : ℝ) =
      (Nat.choose (Finset.univ : Finset (Fin n)).card 2 : ℝ) := by
    exact_mod_cast hsum
  linarith

/-- The first pass's statement (`conjectures/162.lean`), with the page's closed range
$0\le\alpha\le1/2$, is **false**: at $\alpha=1/2$ it would need $n+1\le(c+1)\log n$ for all large
$n$ (PROVED in Lean, from `F_half`). -/
theorem erdos_problem_162.variants.first_pass_false :
    ¬ (∀ α : ℝ, 0 ≤ α → α ≤ 1 / 2 →
      ∃ c : ℝ, 0 < c ∧
        ∀ ε : ℝ, 0 < ε →
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            (c - ε) * Real.log (n : ℝ) ≤ (F_erdos162 n α : ℝ) ∧
            (F_erdos162 n α : ℝ) ≤ (c + ε) * Real.log (n : ℝ)) := by
  intro h
  obtain ⟨c, hc, hce⟩ := h (1 / 2) (by norm_num) le_rfl
  obtain ⟨N₀, hN₀⟩ := hce 1 one_pos
  have hK : 0 < c + 1 := by linarith
  set n : ℕ := max N₀ ⌈(2 * (c + 1)) ^ 2⌉₊ with hn
  have hnN : N₀ ≤ n := le_max_left _ _
  have hn2 : (2 * (c + 1)) ^ 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right _ _)
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn2
  obtain ⟨-, hup⟩ := hN₀ n hnN
  rw [erdos_problem_162.F_half] at hup
  push_cast at hup
  have hs : 2 * (c + 1) ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn2
    rwa [Real.sqrt_sq (by linarith)] at this
  have hlog : Real.log n ≤ 2 * (Real.sqrt n - 1) := by
    have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hnpos)
    rw [Real.log_sqrt hnpos.le] at this
    linarith
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have h3 : (c + 1) * Real.log n ≤ (c + 1) * (2 * (Real.sqrt n - 1)) :=
    mul_le_mul_of_nonneg_left hlog hK.le
  have h4 : 2 * (c + 1) * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n :=
    mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
  nlinarith

/-- The page's remark (SOLVED, by the probabilistic method and Ramsey's theorem; not proved here):
for $0\le\alpha<1/2$ there are $c_1,c_2>0$ with $c_1\log n<F(n,\alpha)<c_2\log n$ for all large
$n$. The lower bound already holds at $\alpha=0$ (a colouring of $K_n$ with no monochromatic set of
size $m$ needs $n<R(m)\le4^m$); the upper bound is a union bound over random colourings. -/
theorem erdos_problem_162.variants.bounds :
    ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c₁ * Real.log (n : ℝ) < (F_erdos162 n α : ℝ) ∧
      (F_erdos162 n α : ℝ) < c₂ * Real.log (n : ℝ) :=
  sorry

end
