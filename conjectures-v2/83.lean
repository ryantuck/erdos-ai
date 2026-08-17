import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

open Finset

/--
Erdős Problem #83 [Er71, p.106][Er90][Er92e][Er95]:

Suppose that we have a family $\mathcal{F}$ of subsets of $[4n]$ such that
$|A| = 2n$ for all $A \in \mathcal{F}$ and for every $A, B \in \mathcal{F}$ we
have $|A \cap B| \geq 2$. Then
$$|\mathcal{F}| \leq \frac{1}{2}\left(\binom{4n}{2n} - \binom{2n}{n}^2\right).$$

Conjectured by Erdős, Ko, and Rado [ErKoRa61] (this is the $t = 2$ intersection
conjecture from their 1961 paper — the classical Erdős–Ko–Rado theorem proper is
the $t = 1$ case). Proved by Ahlswede and Khachatrian [AhKh97], who more
generally established the complete intersection theorem: for $2 \le t \le k \le m$
and $r \ge 0$ with $\frac{1}{r+1} \le \frac{m-2k+2t-2}{(t-1)(k-t+1)} < \frac{1}{r}$,
the largest family of $k$-subsets of $[m]$ with pairwise intersections of size
$\ge t$ consists of all $k$-subsets containing at least $t+r$ elements of
$\{1, \ldots, t+2r\}$. Problem #83 is the case $m = 4n$, $k = 2n$, $t = 2$.

Status: SOLVED (proved in the affirmative; the problem carried a \$500 reward).
Source: erdosproblems.com/83 (recovered from archived pipeline session logs);
status confirmed "proved" by the teorth/erdosproblems metadata mirror as of
2026-08-14. Tag: combinatorics. Related OEIS sequences: A071799, A387635.

ℕ-arithmetic notes (verified, so the ℕ subtraction and division below are exact):
$\binom{4n}{2n} \ge \binom{2n}{n}^2$ by the Vandermonde identity
$\binom{4n}{2n} = \sum_k \binom{2n}{k}^2$, and the difference is even for all
$n \ge 1$ (both terms are even, by the fixed-point-free complementation pairing
$A \mapsto [4n] \setminus A$), so `/ 2` divides exactly.

References (journal/pages recovered from the archived page; volume numbers are
corroborated only by the styled sibling file `deepmind/deepmind/83.lean` in this
corpus, not by the recovered page extraction):

[ErKoRa61] Erdős, P., Ko, C., and Rado, R., _Intersection theorems for systems
of finite sets_. Quart. J. Math. Oxford Ser. (2) 12 (1961), 313-320.

[AhKh97] Ahlswede, R. and Khachatrian, L.H., _The complete intersection theorem
for systems of finite sets_. European J. Combin. 18 (1997), 125-136.

[Er71] Erdős, P., _Topics in combinatorial analysis_ (1971), p.106.

[Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
Erdős (1990), 467-478.

[Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and
combinatorics_. Eureka (1992), 44-48.

[Er95] Erdős, P., _Some of my favourite problems in various branches of
combinatorics_. Combinatorics '94 (Catania), Congressus Numerantium 107 (1995).
-/
theorem erdos_problem_83 :
    ∀ n : ℕ, 0 < n →
    ∀ F : Finset (Finset (Fin (4 * n))),
      (∀ A ∈ F, A.card = 2 * n) →
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ 2) →
      F.card ≤ (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2 :=
  sorry

/--
The bound in Problem #83 is best possible (page-confirmed): taking $\mathcal{F}$
to be the collection of all subsets of $[4n]$ of size $2n$ containing at least
$n+1$ elements from $[2n]$ gives a family with pairwise intersections of size
$\ge 2$ (two such sets meet inside $[2n]$ in at least $(n+1)+(n+1)-2n = 2$
elements) and cardinality exactly
$\sum_{i=n+1}^{2n} \binom{2n}{i}^2 = \frac{1}{2}\left(\binom{4n}{2n} - \binom{2n}{n}^2\right).$

Equality was additionally verified by brute force for $n = 1$ (family size $1$)
and $n = 2$ (family size $17$) during review.

NOTE: this variant statement was added at review time from the recovered source
page and is NOT compile-verified.
-/
theorem erdos_problem_83_best_possible :
    ∀ n : ℕ, 0 < n →
    ∃ F : Finset (Finset (Fin (4 * n))),
      (∀ A ∈ F, A.card = 2 * n) ∧
      (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≥ 2) ∧
      F.card = (Nat.choose (4 * n) (2 * n) - Nat.choose (2 * n) n ^ 2) / 2 :=
  sorry
