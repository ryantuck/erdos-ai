import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic

open Finset Equiv

noncomputable section

/-!
# Erdős Problem #1161

Let $f_k(n)$ count the number of elements of $S_n$ (the symmetric group) of
order $k$. For which values of $k$ will $f_k(n)$ be maximal?

Status: SOLVED (erdosproblems.com/1161, banner tooltip: "This has been
resolved in some other way than a proof or disproof."; page last edited
01 February 2026, accessed 2026-02-23; cross-checked against the
teorth/erdosproblems metadata mirror: state "solved", last update 2026-01-26).
Tags: group theory. Related OEIS sequences: listed as "Possible" (none
specified). Additional thanks to: Quanyu Tang.

Beker [Be25d] proved that
$$\max_{k \geq 1} f_k(n) \sim (n-1)!,$$
and that if $n$ is sufficiently large and $f_k(n) \geq (n-1)!$ then
$\operatorname{lcm}(1,\ldots,n-k) \mid k$. The page further states:
"for all large $n$, $f_k(n) = (n-1)!$ if and only if $k \geq 1$ is minimal
such that $\operatorname{lcm}(1,\ldots,n-k) \mid k$."

**Warning (reviewer note):** the page's last displayed claim is literally
false as stated, for every $n \geq 3$. Writing
$k^* = \min\{k \geq 1 : \operatorname{lcm}(1,\ldots,n-k) \mid k\}$ (the set
contains $n-1$, since $\operatorname{lcm}(1,\ldots,1) = 1 \mid n-1$, so
$k^* \leq n-1$; and $k^* > n/2$ for large $n$ since
$\operatorname{lcm}(1,\ldots,n-k) \mid k$ forces
$\operatorname{lcm}(1,\ldots,n-k) \leq k$), the permutations formed by a
$k^*$-cycle together with an arbitrary permutation of the remaining
$n - k^*$ points all have order exactly $k^*$ (every permutation of
$m = n - k^*$ points has order dividing $\operatorname{lcm}(1,\ldots,m)$,
which divides $k^*$), and there are $n!/k^* \geq n!/(n-1) > (n-1)!$ of them.
So $f_{k^*}(n) > (n-1)!$ and equality fails at $k = k^*$ itself.
Concretely: $n = 6$ has $k^* = 4$ and $f_4(6) = 180 \neq 120 = 5!$;
$n = 7$ has $k^* = 6$ and $f_6(7) = 1470 \neq 720 = 6!$. The forward
direction fails too: for prime $n$, $f_n(n) = (n-1)!$ (exactly the
$n$-cycles) yet $n$ is not minimal. The intended (and consistent) reading of
Beker's characterization — the answer to the problem's actual question, and
the content of [Be25d] per its title — is that for all large $n$ the
*maximizing* $k$ is exactly the minimal $k \geq 1$ with
$\operatorname{lcm}(1,\ldots,n-k) \mid k$; that corrected statement is
formalized in `erdos_problem_1161.variants.characterization`. The literal
paper statement could not be checked offline (arXiv unreachable from this
container).

References:

[Va99] Various, "Some of Paul's favorite problems". Booklet produced for the
conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
§5.72. (Identification per the upstream formal-conjectures contribution
guide's worked example — copied from the site's "View the LaTeX source"
section — and 20+ sibling problems in this corpus; the section number 5.72 is
from the recovered page's [Va99,5.72] citation link. The "Vardi, I.,
*Computational Recreations in Mathematica*" expansion appearing in the
archived styled file is unsupported by any recovered source and is not
carried here.)

[Be25d] Beker, A., "The most probable order of a random permutation".
arXiv:2510.11698 (2025). (Per the pipeline's /latex/1161 fetch preserved in
the session logs; arXiv preprint, no journal/volume/pages.)

Tags: group theory
-/

/-- f_k(n): the number of permutations in S_n whose order equals k.

Degenerate values: `countPermsOfOrder n 0 = 0` (every element of a finite
group has positive order, so no permutation has `orderOf` equal to 0), and
`countPermsOfOrder 0 1 = 1` (the trivial group's identity). -/
noncomputable def countPermsOfOrder (n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => orderOf σ = k)).card

/--
Erdős Problem #1161 [Va99, 5.72] — asymptotic magnitude (Solved by Beker
[Be25d]):

Let f_k(n) count the number of elements of S_n of order k. Beker proved that
max_{k ≥ 1} f_k(n) ~ (n-1)!, i.e., the maximum over k of the number of
permutations of order k is asymptotic to (n-1)!.

Formalized as: for every ε > 0, for all sufficiently large n,
(1) there exists k ≥ 1 with f_k(n) ≥ (1 - ε) · (n-1)!, and
(2) for all k, f_k(n) ≤ (1 + ε) · (n-1)!.

This formalizes only the magnitude of the maximum. The answer to the
problem's actual question — *which* k maximize f_k(n) — is formalized in
`erdos_problem_1161.variants.characterization`.
-/
theorem erdos_problem_1161 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
        (∃ k : ℕ, k ≥ 1 ∧
          (countPermsOfOrder n k : ℝ) ≥ (1 - ε) * ((n - 1).factorial : ℝ)) ∧
        (∀ k : ℕ,
          (countPermsOfOrder n k : ℝ) ≤ (1 + ε) * ((n - 1).factorial : ℝ)) :=
  sorry

/--
Beker's necessary divisibility condition (Solved, [Be25d]; verbatim from the
source page): if n is sufficiently large and f_k(n) ≥ (n-1)!, then
lcm(1, …, n-k) ∣ k.

The divisibility lcm(1, …, m) ∣ k is encoded equivalently as
"every d with 1 ≤ d ≤ m divides k" (the lcm is the least common multiple of
exactly these d). For k ≥ n the range [1, n-k] is empty under ℕ-subtraction
and the condition holds vacuously — matching the empty-lcm convention
lcm(∅) = 1, which the source statement itself needs: f_n(n) ≥ (n-1)!
(the n-cycles), so k = n must satisfy the conclusion.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1161.variants.divisibility_necessary :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ k : ℕ, (n - 1).factorial ≤ countPermsOfOrder n k →
        ∀ d : ℕ, 1 ≤ d → d ≤ n - k → d ∣ k :=
  sorry

/--
Beker's characterization of the maximizing k (Solved, [Be25d]), in the
corrected maximality form: for all sufficiently large n, f_k(n) is maximal
(that is, f_j(n) ≤ f_k(n) for every j) if and only if k is the minimal
k' ≥ 1 such that lcm(1, …, n-k') ∣ k'.

This — not the literal equality "f_k(n) = (n-1)!" displayed on the source
page — is the answer to the problem's question "for which values of k will
f_k(n) be maximal?". The displayed equality version is provably false for
every n ≥ 3: at the minimal k* itself, f_{k*}(n) ≥ n!/k* > (n-1)!
(k*-cycle plus arbitrary permutation of the remaining n - k* points; e.g.
f_4(6) = 180 ≠ 120 = 5!), and for prime n, f_n(n) = (n-1)! holds at the
non-minimal k = n. See the module docstring for the full argument. The
corrected reading is consistent with all computed data (argmax f_k(n) = k*
for n = 5, 7, 8) and with the title of [Be25d]; the paper itself was not
reachable offline to confirm its exact phrasing.

lcm(1, …, m) ∣ k is encoded as "every d with 1 ≤ d ≤ m divides k", as in
`erdos_problem_1161.variants.divisibility_necessary`. At k = 0 both sides of
the iff are false (f_0(n) = 0 is not maximal for n ≥ 2, and 1 ≤ k fails), so
quantifying k over all of ℕ is harmless.

Added by the fable-review pass; not compile-verified.
-/
theorem erdos_problem_1161.variants.characterization :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∀ k : ℕ,
        (∀ j : ℕ, countPermsOfOrder n j ≤ countPermsOfOrder n k) ↔
          (1 ≤ k ∧ (∀ d : ℕ, 1 ≤ d → d ≤ n - k → d ∣ k) ∧
            ∀ k' : ℕ, 1 ≤ k' → (∀ d : ℕ, 1 ≤ d → d ≤ n - k' → d ∣ k') →
              k ≤ k') :=
  sorry

end
