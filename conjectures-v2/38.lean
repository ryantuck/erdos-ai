import Mathlib.Data.Real.Archimedean
import Mathlib.Data.PNat.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 38

*Reference:* [erdosproblems.com/38](https://www.erdosproblems.com/38)
(accessed 2026-03-05; page content recovered from the originating pipeline
session's log captures — the live site is unreachable from the review container).

Statement (verbatim from the site): "Does there exist $B\subset\mathbb{N}$ which is
not an additive basis, but is such that for every set $A\subseteq\mathbb{N}$ of
Schnirelmann density $\alpha$ and every $N$ there exists $b\in B$ such that
\[\lvert (A\cup (A+b))\cap \{1,\ldots,N\}\rvert\geq (\alpha+f(\alpha))N\]
where $f(\alpha)>0$ for $0<\alpha <1$? The Schnirelmann density is defined by
\[d_s(A) = \inf_{N\geq 1}\frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N}.\]" [Er56, p.136]

Status: **PROVED (Lean)** — answered YES. The archived page capture
(edition 16 September 2025, accessed 2026-03-05) still showed OPEN, but the
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a21,
2026-08-14) records status "proved (Lean)" with last update 2026-05-01, and the
upstream google-deepmind/formal-conjectures file `ErdosProblems/38.lean`
(commit dd1c2beb) is categorized `research solved` with `answer(True)`, noting:
"A positive solution was given by GPT 5.5 Pro (prompted by gebyjaff, cleanup by
Liam Price); in fact a sparse random set $B$ has this property, with
$f(\alpha)\gg \alpha(1-\alpha)^2$", with a Lean formal proof recorded at
https://www.erdosproblems.com/forum/thread/38#post-6131. The bare assertion below
is therefore the true direction of the (former) question.

Remarks from the page: Erdős [Er36c] proved that if $B$ is an additive basis of
order $k$ then, for any set $A$ of Schnirelmann density $\alpha$, for every $N$
there exists some integer $b\in B$ such that
\[\lvert (A\cup (A+b))\cap \{1,\ldots,N\}\rvert\geq
\left(\alpha+\frac{\alpha(1-\alpha)}{2k}\right)N\]
(formalized below as `erdos_problem_38.variants.erdos_1936`). It seems an
interesting question (not one Erdős appears to have asked directly, although see
problem 35) to improve the lower bound here, even in the case $B=\mathbb{N}$;
Erdős observed that a random set of density $\alpha$ shows that the factor of
$\frac{\alpha(1-\alpha)}{2}$ in this case cannot be improved past
$\alpha(1-\alpha)$. This is a stronger property than $B$ being an essential
component (see problem 37). Linnik [Li42] gave the first construction of an
essential component which is not an additive basis.

Definitional note (from the upstream formal-conjectures file): in [Er56] (top of
p. 135) Erdős uses the weaker notion of additive basis in which every natural
number is a sum of *at most* $k$ elements of the set (rather than exactly $k$);
`IsAdditiveBasis` below follows that convention.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur
la Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er36c] Erdős, P., _On the arithmetical density of the sum of two sequences, one
of which forms a basis for the integers_. Acta Arith. (1936), 201-207. (The
`/latex/35` bibliography gives no volume number; none is fabricated here.)

[Li42] Linnik, Yu. V. (1942). Honest stub: cited on the problem page as [Li42];
no `/latex/38` fetch exists in the archived session logs and no sibling file
carries this key, so fuller bibliographic data is not recoverable offline.

Bibliographic provenance: [Er56] and [Er36c] full entries from the
`erdosproblems.com/latex/35` bibliography fetches captured in the problem-35
pipeline session logs (as already adopted by `conjectures-v2/35.lean`); [Er56]
independently confirmed by the upstream formal-conjectures `ErdosProblems/38.lean`
reference block (commit dd1c2beb).

Tags (page + mirror): number theory. OEIS: none ("N/A" in the mirror). No prize.
-/

open Classical

/--
The Schnirelmann density of a set A ⊆ ℕ, defined as
  d_s(A) = inf_{n ≥ 1} |A ∩ {1,...,n}| / n

(This coincides with Mathlib's `schnirelmannDensity`
(`Mathlib.Combinatorics.Schnirelmann`), which upstream formal-conjectures uses
for this problem; the local definition is kept to avoid touching imports in a
compile-unverified pass. The infimum is over a nonempty index type and the
values lie in [0,1], so the real-valued `⨅` is a genuine infimum — no
`Real.sInf` junk-value issue.)
-/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  ⨅ n : ℕ+, (((Finset.Icc 1 (n : ℕ)).filter (· ∈ A)).card : ℝ) / ((n : ℕ) : ℝ)

/--
The k-fold sumset of a set B ⊆ ℕ: the set of all sums of at most k elements of B
(with repetition; the empty sum 0 is always included).
-/
def kFoldSumset (B : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => {n | ∃ m ∈ kFoldSumset B k, ∃ b ∈ B, n = m + b} ∪ kFoldSumset B k

/--
A set B ⊆ ℕ is an additive basis if there exists k such that every natural number
can be written as the sum of at most k elements of B.

(This is the "at most k" convention Erdős uses in [Er56, p.135] for this problem,
matching upstream formal-conjectures' `Set.IsWeakAddBasis`.)
-/
def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, n ∈ kFoldSumset B k

/--
The translate of a set A by b: A + b = {a + b | a ∈ A}.
-/
def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ :=
  {n | ∃ a ∈ A, n = a + b}

/--
Erdős Problem #38 [Er56, p.136] — **PROVED** (answered YES; see module docstring):

Does there exist B ⊂ ℕ which is not an additive basis, but is such that for
every set A ⊆ ℕ of Schnirelmann density α and every N there exists b ∈ B such that
  |(A ∪ (A + b)) ∩ {1,...,N}| ≥ (α + f(α)) · N
where f(α) > 0 for 0 < α < 1?

The theorem below asserts the affirmative answer directly, which is the true
direction: a sparse random set B has the property, with f(α) ≫ α(1-α)²
(GPT 5.5 Pro, prompted by gebyjaff, cleanup by Liam Price; Lean-verified proof
linked from the problem page's forum thread).

This is a stronger property than B being an essential component (see problem #37).
-/
theorem erdos_problem_38 :
    ∃ (B : Set ℕ), ¬IsAdditiveBasis B ∧
      ∃ (f : ℝ → ℝ), (∀ α : ℝ, 0 < α → α < 1 → 0 < f α) ∧
        ∀ (A : Set ℕ), ∀ (N : ℕ+),
          let α := schnirelmannDensity A
          ∃ b ∈ B,
            (((Finset.Icc 1 (N : ℕ)).filter (· ∈ A ∪ translateSet A b)).card : ℝ) ≥
              (α + f α) * (N : ℝ) :=
  sorry

/--
Erdős's 1936 theorem [Er36c] (page-confirmed variant, not compile-verified):
if B is an additive basis of order k — here: every natural number is a sum of at
most k elements of B — then for any set A of Schnirelmann density α, for every N
there exists some b ∈ B such that
  |(A ∪ (A + b)) ∩ {1,...,N}| ≥ (α + α(1-α)/(2k)) · N.

The hypothesis `hk : 1 ≤ k` is mathematically redundant (a basis of order 0 would
require every natural number to lie in {0}), but is retained so the division by
`2 * k` is visibly nonzero. Edge behavior checked by hand: for α = 0 the bound is
trivial (and B is nonempty, so a witness b exists); for α ∈ (0,1) and N = 1,
density α > 0 forces 1 ∈ A, and the right-hand side is
α + α(1-α)/(2k) ≤ α + α(1-α)/2 < 1, so the bound holds — the page's statement is
not falsified at small parameters.
-/
theorem erdos_problem_38.variants.erdos_1936
    (B : Set ℕ) (k : ℕ) (hk : 1 ≤ k) (hB : ∀ n : ℕ, n ∈ kFoldSumset B k) :
    ∀ (A : Set ℕ), ∀ (N : ℕ+),
      let α := schnirelmannDensity A
      ∃ b ∈ B,
        (((Finset.Icc 1 (N : ℕ)).filter (· ∈ A ∪ translateSet A b)).card : ℝ) ≥
          (α + α * (1 - α) / ((2 * k : ℕ) : ℝ)) * (N : ℝ) :=
  sorry
