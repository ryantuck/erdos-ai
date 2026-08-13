/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1005

*Reference:* [erdosproblems.com/1005](https://www.erdosproblems.com/1005)

Let $a_1/b_1, a_2/b_2, \ldots$ be the Farey fractions of order $n \geq 4$. Let $f(n)$ be
the largest integer such that for all pairs of indices $k < l$ with $l \leq k + f(n)$,
the fractions $a_k/b_k$ and $a_l/b_l$ are "similarly ordered":
$(a_k - a_l)(b_k - b_l) \geq 0$.

Estimate $f(n)$ — in particular, is there a constant $c > 0$ such that
$f(n) = (c + o(1))n$ for all large $n$?

The problem is open. The function $f(n)$ was first considered by Mayer [Ma42], who proved
$f(n) \to \infty$ as $n \to \infty$. Erdős [Er43] proved $f(n) \gg n$. van Doorn [vD25b]
proved $(1/12 - o(1))n \leq f(n) \leq n/4 + O(1)$ and conjectures that the upper bound is
optimal (i.e. $c = 1/4$).

[Er43] Erdős, P., *A note on Farey series*.
Quarterly Journal of Mathematics, Oxford Series (1943), 82–85.

[Ma42] Mayer, A. E., *A mean value theorem concerning Farey series*.
Quarterly Journal of Mathematics, Oxford Series (1942), 48–57.

[vD25b] van Doorn, W., *Improved bounds for the Mayer-Erdős phenomenon on similarly ordered
Farey fractions*. arXiv:2509.00121 (2025).

OEIS sequence: A386893.
-/

open Filter Finset

namespace Erdos1005

/-- The Farey fractions of order $n$: all reduced fractions $a/b \in [0,1]$ with
$b \leq n$, as a sorted list of rationals. -/
def fareyFractions (n : ℕ) : List ℚ :=
  ((Icc 1 n).biUnion fun b =>
    ((range (b + 1)).filter fun a => Nat.Coprime a b).image
      fun (a : ℕ) => (a : ℚ) / (b : ℚ)).sort (· ≤ ·)

/-- Two Farey fractions $p = a_1/b_1$ and $q = a_2/b_2$ (in lowest terms) are
similarly ordered if $(a_1 - a_2)(b_1 - b_2) \geq 0$. -/
def similarlyOrdered (p q : ℚ) : Prop :=
  (p.num - q.num) * ((p.den : ℤ) - q.den) ≥ 0

/-- $f(n)$: the largest $d$ such that for all pairs of indices $i < j$ with $j \leq i + d$
in the Farey sequence of order $n$, the fractions are similarly ordered.

For $n \leq 3$ *every* pair of Farey fractions is similarly ordered, so no largest such
$d$ exists; the defining set is then all of `ℕ` and `sSup` returns the junk value `0`.
This is why the source problem restricts to $n \geq 4$; only large $n$ matter for the
limit below. For $n \geq 4$ the set is a bounded initial segment of `ℕ` (e.g. the pair
$1/4, 2/3 \in F_n$ is not similarly ordered), so `sSup` is the genuine maximum. -/
noncomputable def fareySimOrderFn (n : ℕ) : ℕ :=
  sSup {d : ℕ | ∀ i j : ℕ, i < j → j ≤ i + d →
    ∀ (hi : i < (fareyFractions n).length) (hj : j < (fareyFractions n).length),
    similarlyOrdered ((fareyFractions n).get ⟨i, hi⟩) ((fareyFractions n).get ⟨j, hj⟩)}

/--
Erdős Problem 1005 [Er43]:

Is there a constant $c > 0$ such that $f(n) = (c + o(1))n$ for all large $n$, i.e.
$f(n)/n \to c$ as $n \to \infty$, where $f(n)$ is the largest window size for similarly
ordered Farey fractions of order $n$?

van Doorn [vD25b] proved $(1/12 - o(1))n \leq f(n) \leq n/4 + O(1)$ and conjectures
$c = 1/4$.
-/
@[category research open, AMS 11]
theorem erdos_1005 :
    answer(sorry) ↔
    ∃ c : ℝ, c > 0 ∧
    Tendsto (fun n : ℕ => (fareySimOrderFn n : ℝ) / (n : ℝ)) atTop (nhds c) := by
  sorry

/--
Mayer [Ma42], who first considered the function $f$, proved that
$f(n) \to \infty$ as $n \to \infty$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.mayer :
    Tendsto (fun n : ℕ => fareySimOrderFn n) atTop atTop := by
  sorry

/--
Erdős [Er43] proved that $f(n) \gg n$: there is a constant $c > 0$ such that
$f(n) \geq cn$ for all sufficiently large $n$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.linear_growth :
    ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      c * (n : ℝ) ≤ (fareySimOrderFn n : ℝ) := by
  sorry

/--
van Doorn [vD25b] proved the lower bound $(1/12 - o(1))n \leq f(n)$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.van_doorn_lower :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 / 12 - ε) * (n : ℝ) ≤ (fareySimOrderFn n : ℝ) := by
  sorry

/--
van Doorn [vD25b] proved the upper bound $f(n) \leq n/4 + O(1)$.
-/
@[category research solved, AMS 11]
theorem erdos_1005.variants.van_doorn_upper :
    ∃ C : ℝ, ∀ n : ℕ, (fareySimOrderFn n : ℝ) ≤ (n : ℝ) / 4 + C := by
  sorry

/--
van Doorn [vD25b] conjectures that the upper bound is optimal, i.e. that
$f(n)/n \to 1/4$ as $n \to \infty$.
-/
@[category research open, AMS 11]
theorem erdos_1005.variants.limit_eq_one_quarter :
    Tendsto (fun n : ℕ => (fareySimOrderFn n : ℝ) / (n : ℝ)) atTop (nhds (1 / 4 : ℝ)) := by
  sorry

end Erdos1005
