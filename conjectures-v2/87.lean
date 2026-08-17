import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #87

Verbatim from erdosproblems.com/87 (page edition 17 January 2026, archived captures
accessed 2026-02-22 and 2026-02-23):

"Let ε > 0. Is it true that, if k is sufficiently large, then
  R(G) > (1 - ε)^k · R(k)
for every graph G with chromatic number χ(G) = k?

Even stronger, is there some c > 0 such that, for all large k,
  R(G) > c · R(k)
for every graph G with chromatic number χ(G) = k?"

Here R(G) is the (diagonal) graph Ramsey number: the minimum N such that every
2-colouring of K_N contains a monochromatic copy of G, and R(k) := R(K_k).

**Status: OPEN** (page banner: "This is open, and cannot be resolved with a finite
computation"; confirmed open by the teorth/erdosproblems metadata mirror as of
2026-08-14). Both questions are open; the two theorems below assert the affirmative
direction of each question with `sorry` — the standard encoding for open yes/no
questions in this pipeline (no `answer()` elaborator is available here).

Remarks from the problem page:

* Erdős originally conjectured R(G) ≥ R(k) for every G with χ(G) = k, which is
  trivial for k = 3 but fails already for k = 4: Faudree and McKay [FaMc93] showed
  R(W) = 17 for the pentagonal wheel W (a 6-vertex, 4-chromatic graph), while
  R(4) = 18. The refuted conjecture is recorded below as a negated assertion
  (`erdos_problem_87_original_refuted`).
* Since R(k) ≤ 4^k, the first question is trivial for ε ≥ 3/4.
* Yuval Wigderson points out that R(G) ≫ 2^(k/2) for any G with chromatic number k
  (via a random colouring), which asymptotically matches the best-known lower
  bounds for R(k). Recorded below as `erdos_problem_87_wigderson_lower`.
* This problem is #12 and #13 in the "Ramsey Theory" section of the graphs problem
  collection (mathweb.ucsd.edu/~erdosproblems/, RGLowerBoundByChromaticNumber1/2).

References:

[Er95] Erdős, P. (1995), p. 14. (Problem source. Full bibliographic details not
recoverable from the archived material; sibling files expand this key under several
different titles, so only an honest author-year stub is recorded — DEFERRED.)

[FaMc93] Faudree, R. J. and McKay, B., "A conjecture of Erdős and the Ramsey number
r(W₆)", J. Combinatorial Math. and Combinatorial Computing (1993), 23-31. (Title,
journal, year and pages from the archived /latex/87 extraction; the volume number —
13 per the prior review — is not in the recovered extraction and is left
unconfirmed.)

Tags: graph theory, ramsey theory. Related OEIS sequence: A059442 (possible).

https://www.erdosproblems.com/87
-/

/-- An injective graph homomorphism (embedding) from H into G:
    G contains a copy of H as a (not necessarily induced) subgraph.

    Equivalent to Mathlib's `SimpleGraph.IsContained` (`H ⊑ G`, in
    `Mathlib.Combinatorics.SimpleGraph.Copy`); kept local for a self-contained
    statement. -/
def containsSubgraph {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The (diagonal) graph Ramsey number R(H): the minimum N such that every simple
    graph G on N vertices either contains a copy of H as a subgraph or its
    complement contains a copy of H (equivalently, every 2-colouring of K_N
    contains a monochromatic copy of H).

    Conventions: the defining set is upward closed (restrict any G on N+1 vertices
    to its first N vertices), so `sInf` is its least element, i.e. the genuine
    minimum. For H on a *finite* vertex type the set is nonempty by Ramsey's
    theorem, so no `sInf ∅ = 0` junk arises; for H on an infinite vertex type the
    set is empty and the value is the junk 0 — the theorems below exclude this via
    `[Fintype V]`. Small values: R(K_0) = 0 (empty H is contained vacuously),
    R(K_1) = 1, R(K_2) = 2. -/
noncomputable def graphRamseyNumber {U : Type*} (H : SimpleGraph U) : ℕ :=
  sInf {N : ℕ | ∀ (G : SimpleGraph (Fin N)),
    containsSubgraph G H ∨ containsSubgraph Gᶜ H}

/-- The classical diagonal Ramsey number R(k) := R(K_k, K_k). -/
noncomputable def diagRamsey (k : ℕ) : ℕ :=
  graphRamseyNumber (⊤ : SimpleGraph (Fin k))

/--
**Erdős Problem #87** — Weak form (open):

For every ε ∈ (0, 1), if k is sufficiently large, then R(G) > (1 - ε)^k · R(k)
for every finite graph G with chromatic number χ(G) = k.

Encoding notes. (i) The source is an open yes/no question ("Is it true that…?");
the affirmative direction is asserted, per the pipeline convention for open
questions. (ii) The source says "Let ε > 0"; the hypothesis `ε < 1` restricts to
the intended regime. This is not merely cosmetic: for ε ≥ 2 and even k the factor
(1 - ε)^k = (ε - 1)^k ≥ 1, and G = K_k (with R(G) = R(k)) falsifies the
unrestricted statement — while the page itself notes the question is trivial for
ε ≥ 3/4. Restricting to ε ∈ (0, 1) loses nothing (the question is monotone: smaller
ε is stronger) and matches the source's intent. (iii) The `∃ K` ("sufficiently
large") also absorbs the k = 0 degeneracy, where G = empty graph has χ(G) = 0,
R(G) = 0, (1 - ε)^0 · R(0) = 0, and the strict inequality 0 < 0 would fail.
-/
theorem erdos_problem_87_weak :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      (diagRamsey k : ℝ) * (1 - ε) ^ k < (graphRamseyNumber G : ℝ) :=
  sorry

/--
**Erdős Problem #87** — Strong form (open):

There exists c > 0 such that for all sufficiently large k and every finite graph G
with chromatic number χ(G) = k, we have R(G) > c · R(k).

Encoding notes. The source is an open yes/no question ("is there some c > 0…?");
the affirmative direction is asserted, per the pipeline convention for open
questions. The quantifier order (∃ c before ∀ k) makes c an absolute constant, as
the source requires. The `∃ K` absorbs the k = 0 degeneracy (empty graph, see the
weak form). The strong form implies the weak form: given c, choose K with
(1 - ε)^K < c; then (1 - ε)^k R(k) < c · R(k) < R(G) for all k ≥ K.
-/
theorem erdos_problem_87_strong :
    ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      c * (diagRamsey k : ℝ) < (graphRamseyNumber G : ℝ) :=
  sorry

/--
**Erdős Problem #87** — Original conjecture, refuted [FaMc93]:

Erdős originally conjectured that R(G) ≥ R(k) for every graph G with chromatic
number χ(G) = k. This is trivial for k = 3 but false for k = 4: Faudree and McKay
showed R(W) = 17 for the pentagonal wheel W (the 6-vertex wheel over C₅, which is
4-chromatic), while R(4) = 18. Following the direct-assertion convention for
refuted statements, the *negation* of the conjecture is asserted. Quantifying V
over `Type` suffices: the counterexample W lives on `Fin 6`.

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
theorem erdos_problem_87_original_refuted :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V) (k : ℕ),
      G.chromaticNumber = k → diagRamsey k ≤ graphRamseyNumber G) :=
  sorry

/--
**Erdős Problem #87** — Wigderson's lower bound (solved):

Yuval Wigderson observed (via a random colouring) that R(G) ≫ 2^(k/2) for any G
with chromatic number k: there is a constant c > 0 such that for all sufficiently
large k, every finite graph G with χ(G) = k satisfies R(G) ≥ c · 2^(k/2).
To avoid square roots (not imported here), the inequality is stated in the
equivalent squared form c · 2^k ≤ R(G)² (both sides nonnegative, c renamed from
c² — the existential absorbs the renaming).

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
theorem erdos_problem_87_wigderson_lower :
    ∃ c : ℝ, 0 < c ∧
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.chromaticNumber = k →
      c * 2 ^ k ≤ ((graphRamseyNumber G : ℝ)) ^ 2 :=
  sorry

end
