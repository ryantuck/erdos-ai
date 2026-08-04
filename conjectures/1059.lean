import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #1059 [Gu04]:

Are there infinitely many primes $p$ such that $p - k!$ is composite for each
$k$ such that $1 \leq k! < p$?

A question of Erdős reported in problem A2 of Guy's collection [Gu04].
Examples include $p = 101$ and $p = 211$. The problem is OPEN
(erdosproblems.com/1059, accessed 2026-03-06). Related OEIS sequence: A064152.

Compositeness of $m = p - k!$ is encoded as $1 < m \land \neg(m$ prime$)$:
since $1$ is neither prime nor composite, a prime of the form $p = k! + 1$
(e.g. $p = 2$) must fail the condition at the factorial $k! = p - 1$, which
`¬ m.Prime` alone would not capture. This matches `Nat.Composite` as used by
the upstream formalization in google-deepmind/formal-conjectures
(`FormalConjectures/ErdosProblems/1059.lean`), where that predicate is defined
as `1 < n ∧ ¬ n.Prime`.

The hypothesis `1 ≤ k.factorial` mirrors the source's "$1 \leq k! < p$"; it is
automatically true (`Nat.factorial_pos`) and kept only for fidelity to the
source phrasing.

[Gu04] Guy, R., *Unsolved Problems in Number Theory*, 3rd edition, Springer,
2004. (Reference data from sibling files in this repo; page/edition details
not independently verified against `erdosproblems.com/latex/1059`.)
-/
theorem erdos_problem_1059 :
    Set.Infinite {p : ℕ | Nat.Prime p ∧
      ∀ k : ℕ, 1 ≤ k.factorial → k.factorial < p →
        1 < p - k.factorial ∧ ¬ (p - k.factorial).Prime} :=
  sorry

/--
Erdős Problem #1059, suggested easier variant [Gu04]:

Erdős suggested it may be easier to show that there are infinitely many $n$
such that, if $l! < n \leq (l+1)!$, then all the prime factors of $n$ are
$> l$, and all the numbers $n - k!$ are composite for $1 \leq k \leq l$.

For each $n \geq 2$ there is exactly one $l \geq 1$ with $l! < n \leq (l+1)!$
(and no such $l$ for $n \in \{0, 1\}$), so the existential encoding below
captures the intended statement while excluding the degenerate $n \leq 1$.
Compositeness is encoded as $1 < m \land \neg(m$ prime$)$, as in the main
statement. Since $k \leq l$ gives $k! \leq l! < n$, the ℕ-subtraction
$n - k!$ never truncates.
-/
theorem erdos_problem_1059.variants.easier :
    Set.Infinite {n : ℕ | ∃ l : ℕ, l.factorial < n ∧ n ≤ (l + 1).factorial ∧
      (∀ q : ℕ, q.Prime → q ∣ n → l < q) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ l →
        1 < n - k.factorial ∧ ¬ (n - k.factorial).Prime)} :=
  sorry
