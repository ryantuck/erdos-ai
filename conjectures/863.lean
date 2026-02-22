import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Basic

open Finset Classical Filter

noncomputable section

/-!
# Erdős Problem #863

Let $r \geq 2$ and let $A \subseteq \{1, \ldots, N\}$ be a set of maximal size such that
there are at most $r$ solutions to $n = a + b$ with $a \leq b$ for any $n$. (That is,
$A$ is a $B_2[r]$ set.)

Similarly, let $B \subseteq \{1, \ldots, N\}$ be a set of maximal size such that there
are at most $r$ solutions to $n = a - b$ for any nonzero $n$.

If $|A| \sim c_r N^{1/2}$ as $N \to \infty$ and $|B| \sim c_r' N^{1/2}$ as $N \to \infty$
then is it true that $c_r \neq c_r'$ for $r \geq 2$? Is it true that $c_r' < c_r$?

A problem of Erdős [Er92c], first formulated in conversation with Berend, and later
independently reformulated with Freud.

It is known that $c_1 = c_1' = 1$ (the classical bound on Sidon sets).

Tags: number theory, sidon sets, additive combinatorics
-/

/-- The number of representations of `n` as `a + b` with `a ≤ b` and `a, b ∈ S`. -/
noncomputable def sumRepCount863 (S : Finset ℕ) (n : ℕ) : ℕ :=
  S.sum (fun a => (S.filter (fun b => a ≤ b ∧ a + b = n)).card)

/-- `S` is a B₂[r] set if every `n` has at most `r` representations
    as `a + b` with `a ≤ b`, `a, b ∈ S`. -/
def IsB2r863 (r : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount863 S n ≤ r

/-- The maximum cardinality of a B₂[r] subset of {1, …, N}. -/
noncomputable def maxB2rSize863 (r : ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsB2r863 r S)).sup Finset.card

/-- The number of representations of a positive integer `n` as a difference `a - b = n`
    (equivalently, `a = b + n`) with `a, b ∈ S`. -/
noncomputable def diffRepCount863 (S : Finset ℕ) (n : ℕ) : ℕ :=
  S.sum (fun b => (S.filter (fun a => a = b + n)).card)

/-- `S` is difference-r-bounded if every nonzero difference has at most `r`
    representations as `a - b` with `a, b ∈ S`. -/
def IsDiffBounded863 (r : ℕ) (S : Finset ℕ) : Prop :=
  ∀ n : ℕ, n > 0 → diffRepCount863 S n ≤ r

/-- The maximum cardinality of a difference-r-bounded subset of {1, …, N}. -/
noncomputable def maxDiffBoundedSize863 (r : ℕ) (N : ℕ) : ℕ :=
  ((Icc 1 N).powerset.filter (fun S => IsDiffBounded863 r S)).sup Finset.card

/--
Erdős Problem #863, weak form [Er92c]:

If the limits $c_r = \lim_{N \to \infty} f_r^+(N) / \sqrt{N}$ (maximum B₂[r] set size)
and $c_r' = \lim_{N \to \infty} f_r^-(N) / \sqrt{N}$ (maximum difference-r-bounded set
size) both exist, then $c_r \neq c_r'$ for $r \geq 2$.
-/
theorem erdos_problem_863_weak (r : ℕ) (hr : r ≥ 2)
    (c c' : ℝ)
    (hc : Tendsto (fun N => (maxB2rSize863 r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c))
    (hc' : Tendsto (fun N => (maxDiffBoundedSize863 r N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds c')) :
    c ≠ c' :=
  sorry

/--
Erdős Problem #863, strong form [Er92c]:

If the limits $c_r = \lim_{N \to \infty} f_r^+(N) / \sqrt{N}$ (maximum B₂[r] set size)
and $c_r' = \lim_{N \to \infty} f_r^-(N) / \sqrt{N}$ (maximum difference-r-bounded set
size) both exist, then $c_r' < c_r$ for $r \geq 2$.
-/
theorem erdos_problem_863_strong (r : ℕ) (hr : r ≥ 2)
    (c c' : ℝ)
    (hc : Tendsto (fun N => (maxB2rSize863 r N : ℝ) / Real.sqrt (N : ℝ)) atTop (nhds c))
    (hc' : Tendsto (fun N => (maxDiffBoundedSize863 r N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds c')) :
    c' < c :=
  sorry

end
