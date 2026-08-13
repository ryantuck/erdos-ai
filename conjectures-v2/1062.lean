import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.Finset.Card
import Mathlib.NumberTheory.Real.Irrational

/-!
# Erdős Problem #1062

Let $f(n)$ be the size of the largest subset $A \subseteq \{1,\ldots,n\}$ such that
there are no three distinct elements $a, b, c \in A$ such that $a \mid b$ and
$a \mid c$. How large can $f(n)$ be? Is $\lim f(n)/n$ irrational?

Status on erdosproblems.com/1062: OPEN ("This is open, and cannot be resolved with a
finite computation."). Page last edited 06 January 2026; archived captures accessed
2026-02-22 and 2026-03-06 agree verbatim.

The example $[m+1, 3m+2]$ shows that $f(n) \geq \lceil \tfrac{2}{3} n \rceil$.
Lebensold [Le76] has shown that, for large $n$,
$0.6725 n \leq f(n) \leq 0.6736 n$.
This is problem B24 in Guy's collection [Gu04].

Related OEIS sequence (per the problem page): A038372.

[Gu04] Guy, R. K., _Unsolved problems in number theory_, 3rd ed., Springer (2004),
xviii+437. Problem B24. (Bibliographic details from sibling files in this repo;
the site's /bibs data was not recoverable offline.)

[Le76] Lebensold (1976). (Author surname from the problem page and year inferred
from the citation key only; full bibliographic details not recoverable offline —
honest stub, do not treat as verified.)

Note: the authoritative upstream formalization of this problem lives in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1062.lean,
linked from the problem page as "Formalised statement? Yes") and is not present in
this repository. Upstream encodes the irrationality question as
`(∃ l, Tendsto (f n / n) atTop (𝓝 l) ∧ Irrational l) ↔ answer(sorry)`
(`erdos_1062.parts.ii`, category `research open`); the theorem below asserts the
same proposition `P` of that iff directly, in this repo's raw conjecture style.
-/

/--
A finite set A of naturals has a "divisor fork" if there exist three distinct
elements a, b, c ∈ A such that a ∣ b and a ∣ c.
-/
def HasDivisorFork (A : Finset ℕ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ∣ b ∧ a ∣ c

instance : DecidablePred HasDivisorFork := by
  intro A
  unfold HasDivisorFork
  infer_instance

/--
f(n) = the size of the largest subset A ⊆ {1,...,n} with no "divisor fork"
(no element dividing two other distinct elements).

The empty set is always fork-free, so the filtered powerset below is nonempty and
`Finset.sup` returns the genuine maximum; in particular f(0) = 0 with no junk values.
-/
noncomputable def maxNoDivisorForkSize (n : ℕ) : ℕ :=
  Finset.sup
    ((Finset.Icc 1 n).powerset.filter (fun A => ¬ HasDivisorFork A))
    Finset.card

/--
Erdős Problem #1062 [Gu04]:

Let f(n) be the size of the largest subset A ⊆ {1,...,n} such that there are
no three distinct elements a, b, c ∈ A with a ∣ b and a ∣ c.

How large can f(n) be? Is lim f(n)/n irrational?

The problem is OPEN. It is formulated here, in raw conjecture style, as the direct
assertion of the conjectured affirmative answer: the limit lim f(n)/n exists and is
irrational. (The upstream formal-conjectures statement wraps this same proposition
in `↔ answer(sorry)`.)

Lebensold [Le76] showed that for large n, 0.6725n ≤ f(n) ≤ 0.6736n.
-/
theorem erdos_problem_1062 :
    ∃ α : ℝ, Irrational α ∧
      Filter.Tendsto (fun n => (maxNoDivisorForkSize n : ℝ) / (n : ℝ))
        Filter.atTop (nhds α) :=
  sorry

/--
The interval $\{\lfloor n/3 \rfloor + 1, \ldots, n\}$ has no divisor fork: each of
its elements $a$ satisfies $3a > n$, so at most one multiple of $a$ (namely $2a$)
lies in the interval. Its size is $n - \lfloor n/3 \rfloor = \lceil 2n/3 \rceil$,
whence $f(n) \geq \lceil \tfrac{2}{3} n \rceil$ for every $n$ — the problem page
phrases this via the example $[m+1, 3m+2]$. Since $f(n)$ is an integer,
$f(n) \geq \lceil 2n/3 \rceil$ is equivalent to the ceiling-free inequality
$2n \leq 3 f(n)$ used below.
-/
theorem erdos_problem_1062.variants.lower_bound (n : ℕ) :
    2 * n ≤ 3 * maxNoDivisorForkSize n :=
  sorry

/--
Lebensold [Le76] has shown that, for large $n$,
$0.6725 n \leq f(n) \leq 0.6736 n$.
-/
theorem erdos_problem_1062.variants.lebensold :
    ∀ᶠ (n : ℕ) in Filter.atTop,
      (0.6725 : ℝ) * (n : ℝ) ≤ (maxNoDivisorForkSize n : ℝ) ∧
      (maxNoDivisorForkSize n : ℝ) ≤ (0.6736 : ℝ) * (n : ℝ) :=
  sorry
