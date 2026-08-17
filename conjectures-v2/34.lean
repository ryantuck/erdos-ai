import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

/-!
# Erdős Problem 34

*Reference:* [erdosproblems.com/34](https://www.erdosproblems.com/34)
(accessed 2026-02-22, page edition 27 December 2025; page content recovered from two
agreeing archived session-log captures — the live site is unreachable from the review
container).

Statement (verbatim from the site): "For any permutation $\pi\in S_n$ of
$\{1,\ldots,n\}$ let $S(\pi)$ count the number of distinct consecutive sums, that is,
sums of the shape $\sum_{u\leq i\leq v}\pi(i)$. Is it true that
\[S(\pi) = o(n^2)\]
for all $\pi\in S_n$?" [Er77c, p.71] [ErGr80, p.58]

Status: **DISPROVED (LEAN)** ("This has been solved in the negative and the proof
verified in Lean"). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
checked at commit a09c7a21, 2026-08-14) agrees: status "disproved (Lean)" (last update
2026-02-05); tags: number theory; OEIS: A389241, A234813, A390187; no prize.

Remarks from the page: it is easy to see that $S(\iota)=o(n^2)$ if $\iota$ denotes the
identity permutation; motivated by this, Erdős asked if this remains true for all
permutations. The first counterexample was provided by Hegyvári [He86], who constructed
a permutation with $S(\pi) \geq (1/18+o(1))n^2$. In fact this conjecture is extremely
false, as shown by Konieczny [Ko15], who both constructs an explicit permutation with
$S(\pi) \geq n^2/4$, and also shows that for a random permutation
$S(\pi)\sim \frac{1+e^{-2}}{4}n^2$ (probabilistic; not formalized here — it needs
measure-theoretic machinery not present in this file). For
$f(n)=\max_{\pi\in S_n}S(\pi)$, Konieczny [Ko15] proves
$(0.286\cdots)n^2\leq f(n) \leq (0.446\cdots)n^2$. For $g(n)=\min S(\pi)$, Konieczny
shows $g(n) \gg n^{3/2}$, and it may be true that $g(n)\geq n^{2-o(1)}$, or even
$g(n) \gg S(\iota)$ (speculative — "it may be true" — so recorded here only, not
formalized). See also Erdős problems 356 and 357. Additional thanks: Wouter van Doorn.

[Er77c] Erdős, P., _Problems and results on combinatorial number theory. III._.
Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976) (1977), 43–72.

[ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in combinatorial
number theory_. Monographies de L'Enseignement Mathématique **28** (1980).

[He86] Hegyvári, N., _On consecutive sums in sequences_. Acta Math. Hungar. (1986),
193–200. (Volume number not recoverable offline and not fabricated.)

[Ko15] Konieczny, J., _On consecutive sums in permutations_. arXiv:1504.07156 (2015).

Bibliographic provenance: [He86] pages and the [Ko15] title/arXiv id are from the
original pipeline's logged fetch of `erdosproblems.com/latex/34`; [Er77c] and [ErGr80]
are the canonical entries shared across this corpus's sibling files and the upstream
google-deepmind/formal-conjectures repository (checked at commit dd1c2beb). Note the
first-pass docstring cited [Ko15] under the incorrect title "Consecutive sums in a
random permutation"; the `/latex/34` source gives "On consecutive sums in permutations".
-/

open Finset BigOperators Equiv

/--
For a permutation σ of Fin n, the set of distinct consecutive sums.
A consecutive sum is ∑_{i ∈ [u,v]} (σ(i) + 1) for u ≤ v in Fin n,
corresponding to summing consecutive values of a permutation of {1,...,n}.
-/
noncomputable def consecutiveSums (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  ((Finset.univ (α := Fin n)) ×ˢ (Finset.univ (α := Fin n))).filter (fun p => p.1 ≤ p.2)
    |>.image (fun p => ∑ i ∈ Finset.Icc p.1 p.2, ((σ i).val + 1))

/--
Erdős Problem #34 [Er77c, p.71; ErGr80, p.58] (DISPROVED):

> For any permutation π ∈ S_n of {1,...,n} let S(π) count the number of distinct
> consecutive sums, that is, sums of the shape ∑_{u ≤ i ≤ v} π(i). Is it true that
> S(π) = o(n²) for all π ∈ S_n?

The answer is **no**: the first counterexample was provided by Hegyvári [He86], who
constructed a permutation with S(π) ≥ (1/18 + o(1))n², and Konieczny [Ko15] showed the
conjecture is extremely false (an explicit permutation with S(π) ≥ n²/4, and
S(π) ∼ (1+e⁻²)/4 · n² for a random permutation).

This direct assertion states the true (refuted) direction ([defect] fix, not
compile-verified): it is the exact logical negation of the uniform little-o statement
`∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ σ, S(σ) ≤ ε n²` that the question asks about (and which the
first-pass file wrongly asserted). Witness: by [He86] any ε < 1/18 works — for large n
Hegyvári's permutation has S(π) ≥ (1/18 + o(1))n² > ε n²; Konieczny's explicit
permutation even allows any ε < 1/4. The uniform encoding is equivalent to the
per-sequence reading "S(πₙ) = o(n²) for every sequence πₙ ∈ Sₙ": its failure at a
single ε yields a sequence of witnessing permutations for infinitely many n (extended
arbitrarily elsewhere), and conversely.
-/
theorem erdos_problem_34 :
  ∃ ε : ℝ, 0 < ε ∧
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      ∃ σ : Equiv.Perm (Fin n),
        ε * (n : ℝ) ^ 2 < ((consecutiveSums n σ).card : ℝ) :=
sorry

/--
Page-confirmed remark (not compile-verified): for the identity permutation ι
(here `(1 : Equiv.Perm (Fin n))`, i.e. position i holds value i+1), S(ι) = o(n²).
The page calls this "easy to see"; it is what motivated Erdős's question.
-/
theorem erdos_problem_34.variants.identity :
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ((consecutiveSums n 1).card : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
sorry

/--
Hegyvári's counterexample [He86] (page-confirmed variant, not compile-verified):
there are permutations with S(π) ≥ (1/18 + o(1))n², i.e. for every ε > 0 and all
sufficiently large n some σ ∈ S_n has S(σ) ≥ (1/18 − ε)n².
-/
theorem erdos_problem_34.variants.hegyvari :
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ σ : Equiv.Perm (Fin n),
        (1 / 18 - ε) * (n : ℝ) ^ 2 ≤ ((consecutiveSums n σ).card : ℝ) :=
sorry

/--
Konieczny's explicit construction [Ko15] (page-confirmed variant, not
compile-verified): an explicit permutation with S(π) ≥ n²/4. The page states the bound
without an explicit range of n; the eventual form below is the safe reading of the
asymptotic claim.
-/
theorem erdos_problem_34.variants.konieczny_explicit :
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ σ : Equiv.Perm (Fin n),
      (n : ℝ) ^ 2 / 4 ≤ ((consecutiveSums n σ).card : ℝ) :=
sorry

/--
Konieczny's bounds on f(n) = max_{π ∈ S_n} S(π) [Ko15] (page-confirmed variant, not
compile-verified): (0.286⋯)n² ≤ f(n) ≤ (0.446⋯)n². The page truncates both constants
with an ellipsis, so only the displayed digits are used here, in the direction they
guarantee: the true lower constant 0.286⋯ is ≥ 0.286 and the true upper constant
0.446⋯ is < 0.447. The max/min over S_n is encoded pointwise: a witness permutation
for the lower bound, all permutations for the upper bound.
-/
theorem erdos_problem_34.variants.konieczny_max_bounds :
  ∃ c₁ c₂ : ℝ, (0.286 : ℝ) ≤ c₁ ∧ c₂ < (0.447 : ℝ) ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (∃ σ : Equiv.Perm (Fin n),
        c₁ * (n : ℝ) ^ 2 ≤ ((consecutiveSums n σ).card : ℝ)) ∧
      (∀ σ : Equiv.Perm (Fin n),
        ((consecutiveSums n σ).card : ℝ) ≤ c₂ * (n : ℝ) ^ 2) :=
sorry

/--
Konieczny's lower bound on g(n) = min_{π ∈ S_n} S(π) [Ko15] (page-confirmed variant,
not compile-verified): g(n) ≫ n^{3/2}, i.e. there is c > 0 with S(σ) ≥ c·n^{3/2} for
every σ ∈ S_n and all large n. Since this file imports no `Real.sqrt`/`rpow`, the
half-integer power is encoded by squaring: for nonnegative quantities,
S(σ) ≥ c·n^{3/2} ⟺ S(σ)² ≥ c²·n³, so the statement below (with constant c² renamed
to c) is exactly the ≫ n^{3/2} bound.
-/
theorem erdos_problem_34.variants.konieczny_min_lower :
  ∃ c : ℝ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ σ : Equiv.Perm (Fin n),
        c * (n : ℝ) ^ 3 ≤ ((consecutiveSums n σ).card : ℝ) ^ 2 :=
sorry
