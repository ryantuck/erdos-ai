-- [AI - Claude Opus 5.5]: Erdős Problem 161 — second-pass formalization
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #161

*Source:* [erdosproblems.com/161](https://www.erdosproblems.com/161) (status **OPEN**: "This is
open, and cannot be resolved with a finite computation."; prize \$500; captured 2026-02-20; page
edited 16 January 2026). [Er90b, p.21]

Let $\alpha\in[0,1/2)$ and $n,t\geq 1$. Let $F^{(t)}(n,\alpha)$ be the smallest $m$ such that we
can $2$-colour the edges of the complete $t$-uniform hypergraph on $n$ vertices such that if
$X\subseteq [n]$ with $\lvert X\rvert \geq m$ then there are at least
$\alpha \binom{\lvert X\rvert}{t}$ many $t$-subsets of $X$ of each colour.

For fixed $n,t$ as we change $\alpha$ from $0$ to $1/2$ does $F^{(t)}(n,\alpha)$ increase
continuously or are there jumps? Only one jump?

Remarks recorded on the page (paraphrased; inequality signs as the page prints them):
* For $\alpha=0$ this is the usual Ramsey function. A conjecture of Erdős, Hajnal and Rado (see
  Problem 562) implies $F^{(t)}(n,0)\asymp\log_{t-1}n$ (the $(t-1)$-fold iterated logarithm).
* "Results of Erdős and Spencer imply that $F^{(t)}(n,\alpha)\gg_\alpha(\log n)^{1/(t-1)}$ for
  all $\alpha>0$, and a similar upper bound holds for $\alpha$ close to $1/2$."
* Erdős in [Er90b]: "If I can hazard a guess completely unsupported by evidence, I am afraid that
  the jump occurs all in one step at $0$. It would be much more interesting if my conjecture would
  be wrong and perhaps there is some hope for this for $t>3$. I know nothing and offer \$500 to
  anybody who can clear up this mystery."
* Conlon, Fox and Sudakov [CFS11]: for any fixed $\alpha>0$, $F^{(3)}(n,\alpha)\ll_\alpha
  \sqrt{\log n}$ (as printed); "coupled with the lower bound above, this implies that there is
  only one jump for fixed $\alpha$ when $t=3$, at $\alpha=0$."
* For all $\alpha>0$ it is known that $F^{(t)}(n,\alpha)\gg_t(\log n)^{c_\alpha}$.
* See also Problem 563 for $t=2$; Problem #40 in Ramsey Theory in the graphs problem collection.

## Which direction is open

With the page's definition, a uniformly random colouring shows
$F^{(t)}(n,\alpha)\le C_{t,\alpha}(\log n)^{1/(t-1)}$ for **every** $\alpha<1/2$: a set $X$ with
$\lvert X\rvert=k$ is unbalanced with probability at most $2^{1-(1-H(\alpha))\binom kt}$ ($H$ the
binary entropy), and a union bound over the at most $n^k$ such sets succeeds once
$\binom kt\gg k\log n$, i.e. $k\gg(\log n)^{1/(t-1)}$. The hard direction is therefore the
**lower** bound: every colouring has a large set in which one colour has density below $\alpha$
(an "almost monochromatic" set, which is what the title of [CFS11] refers to). "The jump occurs all
in one step at $0$" means $F^{(t)}(n,\alpha)\asymp_{t,\alpha}(\log n)^{1/(t-1)}$ for every fixed
$\alpha\in(0,1/2)$, and its open content is the lower bound for $t\ge4$: for $t=2$ it follows
from Ramsey's theorem, and for $t=3$ it is [CFS11]. The page prints the inequalities of its second
and fourth bullets the other way round; read with the page's own definition, the random-colouring
bound is the upper one.

## Encoding notes

* `F_balanced t n α` is `sInf` of a set that always contains `n + 1` (no `X ⊆ Fin n` has more than
  `n` elements), so it is a true minimum and at most `n + 1` (`F_balanced_le`).
* At `α = 0` the page's definition is degenerate as written: "at least $0$" subsets of each colour
  holds for every colouring, so `F_balanced t n 0 = 0` (`F_balanced_zero`). The page's remark that
  $\alpha=0$ gives the Ramsey function needs "at least one" in place of "at least $0$". The
  statements below take $\alpha>0$, where the definition is the intended one.
* `F_balanced` is monotone in `α` (`F_balanced_mono`), as "increase" in the question presumes.
* The main theorem asserts Erdős's guess, the asked direction, while the problem is open. The first
  pass's statement, an upper bound by a power of $\log n$, follows from the random-colouring bound
  and is kept as `variants.first_pass`.

## References

* [Er90b] Erdős, P., _Problems and results on graphs and hypergraphs: similarities and
  differences_. Mathematics of Ramsey theory (1990), 12–28. (From the site's `/latex/161`
  bibliography.)
* [CFS11] Conlon, D., Fox, J. and Sudakov, B., _Large almost monochromatic subsets in
  hypergraphs_. Israel J. Math. (2011), 423–432. (From the site's `/latex/161` bibliography.)
* The results of Erdős and Spencer, and of Erdős, Hajnal and Rado, are cited on the page without
  keys. **DEFERRED:** their sources were not recovered.

*Provenance:* second pass of `conjectures/161.lean` (Opus 5.5 review, `opus-5-5-review/161.md`).
-/

open Finset Real

noncomputable section

/-- A 2-colouring c of the t-element subsets of Fin n is α-balanced at
    threshold m if for every subset X ⊆ Fin n with |X| ≥ m, each colour class
    contains at least α * C(|X|, t) many t-element subsets of X. -/
def IsBalancedColouring (n t m : ℕ) (α : ℝ) (c : Finset (Fin n) → Bool) : Prop :=
  ∀ X : Finset (Fin n), m ≤ X.card →
    ∀ b : Bool,
      α * (Nat.choose X.card t : ℝ) ≤
        (((X.powersetCard t).filter (fun S => c S = b)).card : ℝ)

/-- F^{(t)}(n, α) is the smallest m such that there exists a 2-colouring of the
    t-element subsets of [n] that is α-balanced at threshold m. -/
noncomputable def F_balanced (t n : ℕ) (α : ℝ) : ℕ :=
  sInf { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsBalancedColouring n t m α c }

/--
Erdős Problem #161 [Er90b, p.21] (OPEN, \$500), Erdős's guess "the jump occurs all in one step at
$0$", stated as the open lower bound: for every $t\ge2$ and every fixed $0<\alpha<1/2$ there is
$c>0$ with $F^{(t)}(n,\alpha)\ge c\,(\log n)^{1/(t-1)}$ for all large $n$.

With the known upper bound `variants.random_upper` this says $F^{(t)}(n,\alpha)\asymp
(\log n)^{1/(t-1)}$ for every $\alpha\in(0,1/2)$ (`variants.theta_of_lower_upper`), so the order of
magnitude has a single jump, at $\alpha=0$. The case $t=2$ follows from Ramsey's theorem
(`variants.t_two`) and $t=3$ is [CFS11] (`variants.t_three`); the cases $t\ge4$ are open.
-/
theorem erdos_problem_161 :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1)) ≤ (F_balanced t n α : ℝ) :=
  sorry

/-- `n + 1` always lies in the set whose `sInf` is `F_balanced`: no subset of `Fin n` has more
than `n` elements, so the balance condition is vacuous. Hence `F_balanced t n α ≤ n + 1`, and the
`sInf` is a true minimum (PROVED in Lean). -/
theorem erdos_problem_161.mem_succ (t n : ℕ) (α : ℝ) :
    n + 1 ∈ { m : ℕ | ∃ c : Finset (Fin n) → Bool, IsBalancedColouring n t m α c } := by
  refine ⟨fun _ => true, fun X hX _ => ?_⟩
  have h := X.card_le_univ
  simp only [Fintype.card_fin] at h
  omega

/-- `F_balanced t n α ≤ n + 1` (PROVED in Lean). -/
theorem erdos_problem_161.F_balanced_le (t n : ℕ) (α : ℝ) : F_balanced t n α ≤ n + 1 :=
  Nat.sInf_le (erdos_problem_161.mem_succ t n α)

/-- At `α = 0` the definition as written is degenerate: every colouring is `0`-balanced at
threshold `0`, so `F_balanced t n 0 = 0`. The page's "for $\alpha=0$ this is the usual Ramsey
function" needs "at least one" subset of each colour instead of "at least $0$" (PROVED in Lean). -/
theorem erdos_problem_161.F_balanced_zero (t n : ℕ) : F_balanced t n 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Nat.sInf_le
  exact ⟨fun _ => true, fun X _ b => by simp⟩

/-- `F_balanced` is monotone in `α`: a colouring that is `β`-balanced is `α`-balanced for
`α ≤ β`, so the question's "as we change $\alpha$ from $0$ to $1/2$ does $F$ increase" is about a
nondecreasing function (PROVED in Lean). -/
theorem erdos_problem_161.F_balanced_mono (t n : ℕ) {α β : ℝ} (hαβ : α ≤ β) :
    F_balanced t n α ≤ F_balanced t n β := by
  have hne : ({ m : ℕ | ∃ c : Finset (Fin n) → Bool, IsBalancedColouring n t m β c }).Nonempty :=
    ⟨n + 1, erdos_problem_161.mem_succ t n β⟩
  obtain ⟨c, hc⟩ := Nat.sInf_mem hne
  apply Nat.sInf_le
  refine ⟨c, fun X hX b => le_trans ?_ (hc X hX b)⟩
  exact mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg _)

/-- The first pass's statement (`conjectures/161.lean`): an upper bound for
$F^{(t)}(n,\alpha)$ by a power of $\log n$. It is **not** the open problem: it follows from the
random-colouring bound `variants.random_upper` (`variants.first_pass_of_random_upper`, PROVED in
Lean from it). -/
theorem erdos_problem_161.variants.first_pass :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ D : ℝ, 0 < D ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (F_balanced t n α : ℝ) ≤ C * (Real.log (n : ℝ)) ^ D :=
  sorry

/-- The random-colouring upper bound (SOLVED, classical probabilistic method; not proved here):
for every $t\ge2$ and $0\le\alpha<1/2$, $F^{(t)}(n,\alpha)\le C\,(\log n)^{1/(t-1)}$ for all large
$n$. Sketch: with $N=\binom kt$, at most $2^{H(\alpha)N}$ of the $2^N$ colourings of the $t$-subsets
of a fixed $k$-set give one colour fewer than $\alpha N$ subsets; as $\binom kt\ge(k/t)^t$, a union
bound over the at most $2n^k$ pairs (set, colour) with $k\ge m$ leaves a balanced colouring once
$m^{t-1}\ge t^t(\log_2n+2)/(1-H(\alpha))$. -/
theorem erdos_problem_161.variants.random_upper :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (F_balanced t n α : ℝ) ≤ C * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1)) :=
  sorry

/-- The first pass's statement follows from the random-colouring bound, with
$D=1/(t-1)$ (PROVED in Lean). -/
theorem erdos_problem_161.variants.first_pass_of_random_upper
    (h : ∀ t : ℕ, 2 ≤ t →
      ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (F_balanced t n α : ℝ) ≤ C * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1))) :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ C : ℝ, 0 < C ∧
    ∃ D : ℝ, 0 < D ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (F_balanced t n α : ℝ) ≤ C * (Real.log (n : ℝ)) ^ D := by
  intro t ht α hα0 hα1
  obtain ⟨C, hC, N₀, hN₀⟩ := h t ht α hα0.le hα1
  have ht' : (1 : ℝ) < t := by exact_mod_cast ht
  exact ⟨C, hC, (1 : ℝ) / ((t : ℝ) - 1), by apply div_pos one_pos; linarith, N₀, hN₀⟩

/-- The main theorem together with the random-colouring bound gives the order of magnitude
$F^{(t)}(n,\alpha)\asymp(\log n)^{1/(t-1)}$ for every $\alpha\in(0,1/2)$: the single jump at
$\alpha=0$ that Erdős guessed (PROVED in Lean from the two statements). -/
theorem erdos_problem_161.variants.theta_of_lower_upper
    (hlow : ∀ t : ℕ, 2 ≤ t →
      ∀ α : ℝ, 0 < α → α < 1 / 2 →
      ∃ c : ℝ, 0 < c ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        c * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1)) ≤ (F_balanced t n α : ℝ))
    (hup : ∀ t : ℕ, 2 ≤ t →
      ∀ α : ℝ, 0 ≤ α → α < 1 / 2 →
      ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (F_balanced t n α : ℝ) ≤ C * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1))) :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1)) ≤ (F_balanced t n α : ℝ) ∧
      (F_balanced t n α : ℝ) ≤ C * Real.log (n : ℝ) ^ ((1 : ℝ) / ((t : ℝ) - 1)) := by
  intro t ht α hα0 hα1
  obtain ⟨c, hc, N₁, h₁⟩ := hlow t ht α hα0 hα1
  obtain ⟨C, hC, N₂, h₂⟩ := hup t ht α hα0.le hα1
  exact ⟨c, C, hc, hC, max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_trans (le_max_left _ _) hn), h₂ n (le_trans (le_max_right _ _) hn)⟩⟩

/-- The case $t=2$ of the main theorem (SOLVED, by Ramsey's theorem; not proved here): with
$\alpha>0$ an $\alpha$-balanced colouring at threshold $m$ has no monochromatic set of size
$\max(m,2)$, and every 2-colouring of $K_n$ has one of size $\ge\frac12\log_2n$
(Erdős–Szekeres), so $F^{(2)}(n,\alpha)\gg\log n$. -/
theorem erdos_problem_161.variants.t_two :
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ≤ (F_balanced 2 n α : ℝ) :=
  sorry

/-- The case $t=3$ of the main theorem, Conlon–Fox–Sudakov [CFS11] (SOLVED; not proved here):
every 2-colouring of the triples of $[n]$ has a set of size $c_\alpha\sqrt{\log n}$ in which one
colour has density below $\alpha$, so $F^{(3)}(n,\alpha)\gg_\alpha\sqrt{\log n}$. The page prints
this bound with $\ll$ (see the module docstring). -/
theorem erdos_problem_161.variants.t_three :
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.sqrt (Real.log (n : ℝ)) ≤ (F_balanced 3 n α : ℝ) :=
  sorry

/-- The page's general lower bound (SOLVED per the page; source **DEFERRED**): for every $t$ and
every fixed $\alpha>0$, $F^{(t)}(n,\alpha)\gg_t(\log n)^{c_\alpha}$ for some $c_\alpha>0$. Erdős's
guess is that $c_\alpha=1/(t-1)$ is possible for every $\alpha$. -/
theorem erdos_problem_161.variants.weak_lower :
    ∀ t : ℕ, 2 ≤ t →
    ∀ α : ℝ, 0 < α → α < 1 / 2 →
    ∃ c e : ℝ, 0 < c ∧ 0 < e ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * Real.log (n : ℝ) ^ e ≤ (F_balanced t n α : ℝ) :=
  sorry

end
