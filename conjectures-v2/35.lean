import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem 35

*Reference:* [erdosproblems.com/35](https://www.erdosproblems.com/35)
(accessed 2026-02-22; page content recovered from archived session-log captures — the
live site is unreachable from the review container).

Statement (verbatim from the site): "Let $B\subseteq\mathbb{N}$ be an additive basis
of order $k$ with $0\in B$. Is it true that for every $A\subseteq\mathbb{N}$ we have
\[d_s(A+B)\geq \alpha+\frac{\alpha(1-\alpha)}{k},\] where $\alpha=d_s(A)$ and
\[d_s(A) = \inf \frac{\lvert A\cap\{1,\ldots,N\}\rvert}{N}\] is the Schnirelmann
density?" [Er56]

Status: **PROVED** ("This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, checked at commit
a09c7a21, 2026-08-14) agrees: status "proved" (last update 2025-08-31); tags: number
theory, additive basis; no OEIS references; no prize. The site lists no upstream
formalization ("Formalised statement? No").

Remarks from the page: Erdős [Er36c] proved this is true with $k$ replaced by $2k$ in
the denominator (in a stronger form that only considers $A\cup (A+b)$ for some
$b\in B$; see Erdős Problem 38). Ruzsa has observed that the conjecture follows
immediately from the stronger fact proved by Plünnecke [Pl70] that (under the same
assumptions) $d_s(A+B)\geq \alpha^{1-1/k}$. Additional thanks: Imre Ruzsa.

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
Théorie des Nombres, Bruxelles, 1955 (1956), 127-137.

[Er36c] Erdős, P., _On the arithmetical density of the sum of two sequences, one of
which forms a basis for the integers_. Acta Arith. (1936), 201-207. (The site's
`/latex/35` bibliography gives no volume number; none is fabricated here.)

[Pl70] Plünnecke, H., _Eine zahlentheoretische Anwendung der Graphentheorie_. J.
Reine Angew. Math. 243 (1970), 171-183. (Journal/year/pages as on the site's
`/latex/35` bibliography, which gives no volume number; the volume 243 is the
standard citation of this paper, as already adopted by the archived styled pipeline.)

Bibliographic provenance: [Er56] full entry from the upstream
google-deepmind/formal-conjectures repository (commit dd1c2beb, shared key, e.g.
`FormalConjectures/ErdosProblems/38.lean`); [Er36c] and [Pl70] from the
`erdosproblems.com/latex/35` bibliography fetches captured in the original pipeline
session logs.
-/

open Classical Finset BigOperators

noncomputable section

/-- The sumset A + B: the set of all a + b with a ∈ A, b ∈ B. -/
def sumset35 (A B : Set ℕ) : Set ℕ := {n : ℕ | ∃ a ∈ A, ∃ b ∈ B, n = a + b}

/-- Schnirelmann density of a set A ⊆ ℕ:
    d_s(A) = inf_{N ≥ 1} |A ∩ {1, …, N}| / N -/
noncomputable def schnirelmannDensity (A : Set ℕ) : ℝ :=
  sInf {x : ℝ | ∃ N : ℕ, N ≥ 1 ∧ x = ((Icc 1 N).filter (· ∈ A)).card / (N : ℝ)}

/-- A set B ⊆ ℕ is an additive basis of order k if every natural number
    can be written as a sum of exactly k elements from B (with repetition).
    Since 0 ∈ B is assumed separately, "exactly k" is equivalent to "at most k". -/
def IsAdditiveBasis35 (B : Set ℕ) (k : ℕ) : Prop :=
  ∀ n : ℕ, ∃ f : Fin k → ℕ, (∀ i, f i ∈ B) ∧ ∑ i, f i = n

/--
**Erdős Problem #35** (Proved):

Let B ⊆ ℕ be an additive basis of order k with 0 ∈ B. Is it true that for every
A ⊆ ℕ we have d_s(A + B) ≥ α + α(1 - α)/k, where α = d_s(A) is the
Schnirelmann density?

The problem is from [Er56]. Erdős [Er36c] had proved the bound with k replaced by 2k
in the denominator (in a stronger form that only considers A ∪ (A + b) for some
b ∈ B; see Erdős Problem 38 and `erdos_problem_35.variants.erdos_two_k`). The full
conjecture was proved by Plünnecke [Pl70], who showed the stronger inequality
d_s(A + B) ≥ α^{1-1/k}, as observed by Ruzsa (see
`erdos_problem_35.variants.plunnecke`).

Note: the hypothesis `h0 : 0 ∈ B` is retained for faithfulness to the page's "with
$0 \in B$", although it is entailed by `hB` and `hk` under this file's "exactly k"
basis definition (take n = 0: a sum of k ≥ 1 naturals equal to 0 forces every summand
to be 0).
-/
theorem erdos_problem_35
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis35 B k) (h0 : (0 : ℕ) ∈ B) :
    let α := schnirelmannDensity A
    schnirelmannDensity (sumset35 A B) ≥ α + α * (1 - α) / (k : ℝ) :=
  sorry

/--
Plünnecke's strengthening [Pl70] (page-confirmed variant, not compile-verified):
under the same hypotheses, d_s(A + B) ≥ α^{1-1/k}. Ruzsa observed that Erdős
Problem 35 follows immediately from this (for 0 ≤ α ≤ 1 and k ≥ 1 one has
α^{1-1/k} ≥ α + α(1-α)/k, via α^{-1/k} ≥ 1 + (1/k)·ln(1/α) ≥ 1 + (1/k)(1-α)).

Encoding note: this file imports no real-exponent power (`rpow`), so the inequality
is stated in the equivalent k-th-power form d_s(A + B)^k ≥ α^(k-1) with
natural-number exponents. Equivalence: both densities are nonnegative (each is an
`sInf` of a nonempty set of nonnegative reals), and for x, α ≥ 0 and k ≥ 1 the map
t ↦ t^k is a monotone bijection of [0, ∞), so x ≥ α^{(k-1)/k} ⟺ x^k ≥ α^{k-1}.
The ℕ-subtraction `k - 1` is exact thanks to `hk : k ≥ 1`.
-/
theorem erdos_problem_35.variants.plunnecke
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis35 B k) (h0 : (0 : ℕ) ∈ B) :
    let α := schnirelmannDensity A
    (schnirelmannDensity (sumset35 A B)) ^ k ≥ α ^ (k - 1) :=
  sorry

/--
Erdős's earlier bound [Er36c] (page-confirmed variant, not compile-verified): the
inequality holds with k replaced by 2k in the denominator,
d_s(A + B) ≥ α + α(1 - α)/(2k).

The page states that Erdős proved this in a stronger form that only considers
A ∪ (A + b) for a single b ∈ B (see Erdős Problem 38). The sumset form stated here
is a direct consequence: 0 ∈ B gives A ⊆ A + B and b ∈ B gives A + b ⊆ A + B, so
A ∪ (A + b) ⊆ A + B and the counting function of A ∪ (A + b) is pointwise at most
that of A + B, whence d_s(A + B) ≥ d_s(A ∪ (A + b)).
-/
theorem erdos_problem_35.variants.erdos_two_k
    (A B : Set ℕ) (k : ℕ) (hk : k ≥ 1)
    (hB : IsAdditiveBasis35 B k) (h0 : (0 : ℕ) ∈ B) :
    let α := schnirelmannDensity A
    schnirelmannDensity (sumset35 A B) ≥ α + α * (1 - α) / (2 * k : ℝ) :=
  sorry

end
