import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Erdős Problem #1160

Let $g(n)$ denote the number of groups of order $n$. If $n \le 2^m$ then
$g(n) \le g(2^m)$.

That is, among all orders $n \le 2^m$, the number of isomorphism classes of
groups is maximized at the power of two $2^m$ itself.

Status: OPEN (erdosproblems.com/1160; page last edited 26 January 2026,
accessed 2026-02-23; cross-checked against the teorth/erdosproblems metadata
mirror: state "open", last update 2026-01-23). Tags: group theory. Related
OEIS sequence: A000001 (number of groups of order n).

This is listed as an open problem (Question 22.16) in [BNV07], which reports
it as a "quite natural conjecture, whose origin we have been unable to trace
satisfactorily. We have heard it attributed at various times to various
people, such as Paul Erdős and Graham Higman."

Question 22.18 of [BNV07] suggests the even stronger conjecture
$\sum_{n < 2^m} g(n) \le g(2^m)$ for all sufficiently large $m$ (perhaps even
as soon as $m \ge 7$). (The "sufficiently large" is essential: at $m = 2$ the
sum is $g(1)+g(2)+g(3) = 3 > 2 = g(4)$; the inequality also fails at
$m = 3, 4$.) See `erdos_problem_1160.variants.sum_form`.

Pantelidakis [Pa03] proved that the original conjecture is true if $n$ is odd
and $m \ge 3619$. See `erdos_problem_1160.variants.pantelidakis_odd`.

References:

[Va99] Various, "Some of Paul's favorite problems". Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
§5.71. (Identification recovered from the pipeline logs: the upstream
formal-conjectures contribution guide quotes exactly this entry — copied from
the site's "View the LaTeX source" section — as its worked example, and 20+
sibling problems in this corpus carry the same entry. The section number 5.71
is from the recovered page's [Va99,5.71] citation link. The "Vaughan, R.C."
expansion appearing in the archived styled file is unsupported by any
recovered source and is not carried here.)

[BNV07] Blackburn, S. R., Neumann, P. M., and Venkataraman, G., "Enumeration
of finite groups". Cambridge Tracts in Mathematics, Cambridge University
Press (2007), xii+281 pp. (Authors/title/year/pages per the pipeline's
/latex/1160 fetch preserved in the session logs; the series volume number was
not captured there and is left out rather than invented.)

[Pa03] Pantelidakis, I., "On the number of non-isomorphic groups of the same
order". DPhil thesis, University of Oxford (2003). (Per the pipeline's
/latex/1160 fetch preserved in the session logs.)

Tags: group theory
-/

noncomputable section
open Classical

namespace Erdos1160

/-- Two group structures on the same type are isomorphic if there exists
    a multiplicative equivalence between them. -/
def GroupStructIso (n : ℕ) (G₁ G₂ : Group (Fin n)) : Prop :=
  Nonempty (@MulEquiv (Fin n) (Fin n) G₁.toMul G₂.toMul)

/-- Group isomorphism is an equivalence relation on group structures on Fin n. -/
instance groupStructSetoid (n : ℕ) : Setoid (Group (Fin n)) where
  r := GroupStructIso n
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro G
      exact ⟨@MulEquiv.refl (Fin n) G.toMul⟩
    · intro G₁ G₂ ⟨e⟩
      exact ⟨@MulEquiv.symm (Fin n) (Fin n) G₁.toMul G₂.toMul e⟩
    · intro G₁ G₂ G₃ ⟨e₁⟩ ⟨e₂⟩
      exact ⟨@MulEquiv.trans (Fin n) (Fin n) (Fin n) G₁.toMul G₂.toMul G₃.toMul e₁ e₂⟩

/-- The number of isomorphism classes of groups of order n (OEIS A000001).
    Defined as the cardinality of group structures on Fin n modulo isomorphism.

    Note on semantics: `Group (Fin n)` is a genuinely finite type — its data
    fields beyond `(mul, one, inv)` (`div`, `npow`, `zpow`) are pinned down by
    the propositional axioms, so it injects into a finite type of data — hence
    the quotient is finite and `Nat.card` returns the true count $g(n)$ (with
    the degenerate value `numGroupsOfOrder 0 = 0`, matching A000001's
    $a(0) = 0$, since `Fin 0` carries no group structure). The value of
    `Nat.card` depends only on actual cardinality, not on whether a `Finite`
    instance is derivable by typeclass search. -/
noncomputable def numGroupsOfOrder (n : ℕ) : ℕ :=
  Nat.card (Quotient (groupStructSetoid n))

/--
Erdős Problem #1160 [Va99, 5.71]:

Let g(n) denote the number of groups of order n. If n ≤ 2^m then g(n) ≤ g(2^m).

This conjecture states that among all n ≤ 2^m, the value g(n) is maximized
at n = 2^m (i.e., powers of 2 have the most groups of any order up to that
point). The problem is OPEN. Listed as an open problem (Question 22.16) in
[BNV07], which was "unable to trace [its origin] satisfactorily" and reports
having "heard it attributed at various times to various people, such as Paul
Erdős and Graham Higman."

Tags: group theory
-/
theorem erdos_problem_1160 (n m : ℕ) (h : n ≤ 2 ^ m) :
    numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) :=
  sorry

/--
Question 22.18 of [BNV07] suggests the even stronger conjecture
$$\sum_{n < 2^m} g(n) \le g(2^m)$$
for all sufficiently large $m$ (perhaps even as soon as $m \ge 7$). OPEN.

The "sufficiently large" quantifier is essential and cannot be dropped: the
universal statement is literally false at small $m$, e.g. for $m = 2$ the sum
is $g(1) + g(2) + g(3) = 3 > 2 = g(4)$ (and it also fails at $m = 3$: $9 > 5$,
and $m = 4$: $27 > 14$). The `n = 0` term of `Finset.range` contributes
`numGroupsOfOrder 0 = 0` and is harmless.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1160.variants.sum_form :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∑ n ∈ Finset.range (2 ^ m), numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) :=
  sorry

/--
Pantelidakis [Pa03] proved that the original conjecture is true if $n$ is odd
and $m \ge 3619$: for odd $n \le 2^m$ with $m \ge 3619$, $g(n) \le g(2^m)$.
SOLVED (partial result toward the main conjecture, recorded in the source
page's remarks).

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1160.variants.pantelidakis_odd (n m : ℕ)
    (hodd : Odd n) (h : n ≤ 2 ^ m) (hm : 3619 ≤ m) :
    numGroupsOfOrder n ≤ numGroupsOfOrder (2 ^ m) :=
  sorry

end Erdos1160

end
