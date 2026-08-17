import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Erdős Problem 85

*Reference:* [erdosproblems.com/85](https://www.erdosproblems.com/85)
(accessed 2026-03-05, page last edited 06 December 2025; page content recovered from
archived session-log captures — the live site is unreachable from the review
container).

Statement (verbatim from the site): "Let $n\geq 4$ and $f(n)$ be minimal such that
every graph on $n$ vertices with minimal degree $\geq f(n)$ contains a $C_4$. Is it
true that, for all large $n$, $f(n+1)\geq f(n)$?"
[Er93,p.345][Er94b][Er95][Er96] — tags: graph theory, ramsey theory.

Status: **OPEN**, banner FALSIFIABLE ("Open, but could be disproved with a finite
counterexample."). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
checked at commit a09c7a2, 2026-08-14) agrees: status "open", last update 2026-03-14;
no prize; OEIS A006672; formalized upstream: yes (2025-11-21). The upstream
google-deepmind/formal-conjectures repository has
`FormalConjectures/ErdosProblems/85.lean`, whose statement
`answer(sorry) ↔ ∀ᶠ n in atTop, f n ≤ f (n + 1)` has the same right-hand side as the
theorem below.

Remarks from the page: the function $f(n)$ is a reformulation of the Ramsey number
$R(C_4, K_{1,n})$, in that
$R(C_4,K_{1,n}) = \min\{m : f(m) \leq m-n\}$ and
$f(n) = \min\{m : m \geq R(C_4, K_{1,n-m})\}$; the behaviour of this Ramsey number
more generally is Erdős Problem [552]. A weaker version of the conjecture asks for
some constant $c$ such that $f(m) > f(n) - c$ for all $m > n$ (this question can be
asked for other graphs than $C_4$). The bounds in [552] imply in particular that
$f(n) < \sqrt{n} + 1$ and $f(n) = (1+o(1))\sqrt{n}$. It is easy to check that
$f(4) = 2$. Additional thanks (site): Boris Alexeev. Related OEIS sequence: A006672.

References (no raw `/latex/85` capture survives in the logs; keys from the page
header; sibling-corpus expansions of these Erdős problem-paper keys conflict, so only
honest stubs are recorded — full data DEFERRED, not fabricated):

- [Er93] Erdős, P. (1993), p. 345. (Key-only stub; full data DEFERRED.)
- [Er94b] Erdős, P. (1994). (Key-only stub; full data DEFERRED.)
- [Er95] Erdős, P. (1995). (Key-only stub; full data DEFERRED.)
- [Er96] Erdős, P. (1996). (Key-only stub; full data DEFERRED.)
-/

open SimpleGraph

/--
A simple graph contains a 4-cycle (C₄) if there exist four distinct vertices
a, b, c, d such that a~b, b~c, c~d, d~a.
-/
def SimpleGraph.ContainsCycle4 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b c d : V), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/--
Every simple graph on n vertices with minimum degree ≥ d contains a C₄.
-/
def ForcesCycle4 (n d : ℕ) : Prop :=
  ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ v, d ≤ G.degree v) → G.ContainsCycle4

/--
f(n) is the minimal d such that every graph on n vertices with minimum
degree ≥ d must contain a C₄.

For n ≥ 1 the set below is nonempty (d = n forces vacuously, since no graph on n
vertices has minimum degree n), and it is upward closed, so `sInf` is its least
element — exactly the source's "minimal such that". Small values under this
convention: f(1) = 1, f(2) = 2, f(3) = 3 (vacuous forcing at the maximum possible
degree), and f(4) = 2, agreeing with the problem page; the drop at n = 4 shows the
conjectured monotonicity genuinely needs the "for all large n" qualifier. (For n = 0
the set is empty and `Nat.sInf ∅ = 0`; the theorem below is unaffected.)
-/
noncomputable def minDegreeForCycle4 (n : ℕ) : ℕ :=
  sInf {d : ℕ | ForcesCycle4 n d}

/--
Erdős Problem #85 [Er93,p.345] [Er94b] [Er95] [Er96] (OPEN, FALSIFIABLE):

Let n ≥ 4 and f(n) be minimal such that every graph on n vertices with
minimum degree ≥ f(n) contains a C₄. Is it true that, for all large n,
f(n+1) ≥ f(n)?

The function f(n) is a reformulation of the Ramsey number R(C₄, K_{1,n}):
R(C₄,K_{1,n}) = min{m : f(m) ≤ m − n} and f(n) = min{m : m ≥ R(C₄, K_{1,n−m})};
see Erdős Problem [552] for the behaviour of this Ramsey number in general.
It is known that f(n) < √n + 1, f(n) = (1 + o(1))√n, and f(4) = 2.

Encoding note: the source poses a yes/no question that is open; this direct
assertion states the affirmative (conjectured) direction, per the pipeline
convention for open questions — the page records no belief in the negative, and
the upstream formal-conjectures statement has this same proposition as the
right-hand side of its `answer(sorry) ↔`. The "Let n ≥ 4" of the source needs no
explicit hypothesis here because the claim is asymptotic ("for all large n").
-/
theorem erdos_problem_85 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      minDegreeForCycle4 (n + 1) ≥ minDegreeForCycle4 n :=
  sorry

/--
Weaker version of Erdős Problem #85, from the problem page: "A weaker version of
the conjecture asks for some constant $c$ such that $f(m) > f(n) - c$ for all
$m > n$." (The page adds that this question can be asked for other graphs than
C₄.) Also open.

Encoding: over the integers, f(m) > f(n) − c is equivalent to f(n) < f(m) + c,
which is the form used below to avoid truncated ℕ-subtraction.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_85.variants.weak_monotone :
    ∃ c : ℕ, ∀ n m : ℕ, n < m →
      minDegreeForCycle4 n < minDegreeForCycle4 m + c :=
  sorry

/--
"It is easy to check that $f(4) = 2$" (problem page). Lower bound: the disjoint
union of two edges on 4 vertices has minimum degree 1 and no C₄, so d = 1 does not
force. Upper bound: a graph on 4 vertices with minimum degree ≥ 2 has at least 4
edges, and every such graph (C₄ itself, the diamond K₄ − e, or K₄) contains a C₄.

[Variant added by the Fable review from the recovered page remark; new Lean
statement, not compile-verified.]
-/
theorem erdos_problem_85.variants.f_four : minDegreeForCycle4 4 = 2 :=
  sorry
