-- [AI - Claude Opus 5.5]: Erdős Problem 118 — second-pass formalization
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential
import Mathlib.Order.Hom.Basic

open Ordinal

/-!
# Erdős Problem #118: Partition Ordinals

*Source:* [erdosproblems.com/118](https://www.erdosproblems.com/118) (status **DISPROVED**:
"This has been solved in the negative."; captured 2026-02-20 as the tidied problem box).
[Er87] [Er90] [Er95d] [Er97f]

Let $\alpha$ be a cardinal or ordinal number or an order type such that every two-colouring of
$K_\alpha$ contains either a red $K_\alpha$ or a blue $K_3$. For every $n\geq 3$ must every
two-colouring of $K_\alpha$ contain either a red $K_\alpha$ or a blue $K_n$?

Remarks recorded on the page:
* Such $\alpha$ are called partition ordinals. Conjectured by Erdős and Hajnal. In arrow
  notation, this is asking whether $\alpha \to (\alpha,3)^2$ implies $\alpha \to (\alpha, n)^2$
  for every finite $n$.
* The answer is no, as independently shown by Schipperus [Sc99] (published in [Sc10]) and
  Darby [Da99].
* For example, Larson [La00] has shown that this is false when $\alpha=\omega^{\omega^2}$ and
  $n=5$. There is more background and proof sketches in Chapter 2.9 of [HST10], by Hajnal and
  Larson.
* See also Problems #590, #591 and #592 for more on partition ordinals.

**Encoding.** The formal statements read $\alpha$ as an ordinal, with copies of $\beta$ given
by order embeddings. That is the reading under which the problem is non-trivial. For infinite
cardinals, $\kappa \to (\kappa, \omega)^2$ holds by the Erdős–Dushnik–Miller theorem, so the
implication holds trivially. Since the answer is no, `erdos_problem_118` asserts the negation.

**The counterexample.** $\omega^{\omega^2}$ is a partition ordinal. That is Problem #591,
proved independently by Schipperus [Sc10] and Darby. Larson [La00] showed
$\omega^{\omega^2} \not\to (\omega^{\omega^2}, 5)^2$. See
`erdos_problem_118.variants.omega_omega_sq_partition` and `erdos_problem_118.variants.larson`.

Tags: set theory, ramsey theory.

## References

* [Er87] Erdős, P., _Some problems on finite and infinite graphs_. Logic and combinatorics
  (Arcata, Calif., 1985) (1987), 223–228.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős (1990),
  467–478.
* [Er95d] Erdős, P., _On some problems in combinatorial set theory_. Publ. Inst. Math.
  (Beograd) (N.S.) (1995), 61–65.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Sc99] Schipperus, R. J., _Countable partition ordinals_ (1999), 57.
* [Sc10] Schipperus, R., _Countable partition ordinals_. Ann. Pure Appl. Logic (2010),
  1195–1215.
* [Da99] Darby, C., _Negative partition relations for ordinals $\omega^{\omega^\alpha}$_. J.
  Combin. Theory Ser. B (1999), 205–222.
* [La00] Larson, J. A., _An ordinal partition avoiding pentagrams_. J. Symbolic Logic (2000),
  969–978.
* [HST10] Foreman, M. and Kanamori, A. (eds.), _Handbook of set theory. Vols. 1, 2, 3_ (2010).
  Chapter 2.9 is by Hajnal and Larson.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/118` for [Sc99],
[Sc10], [Da99], [La00] and [HST10]. That extraction gives [Sc99] only as "(1999), 57".
Sibling `/latex` extractions for [Er87], [Er90], [Er95d] and [Er97f].)
-/

/-- The "underlying type" of ordinal `α`: the set of all ordinals strictly less
    than `α`, linearly ordered by the natural ordering on ordinals. -/
abbrev OrdinalSet (α : Ordinal) := {a : Ordinal // a < α}

/-- The ordinal partition relation `α → (β, γ)²`:
    Every 2-coloring of the pairs of elements of `α` (viewed as the linearly
    ordered set `{0, 1, ..., α)`) contains either:
    - an order-embedded copy of `β` whose pairs are all colored 0 (red), or
    - an order-embedded copy of `γ` whose pairs are all colored 1 (blue).

    Here a "copy of β" is given by an order embedding `e : OrdinalSet β ↪o OrdinalSet α`,
    and monochromaticity means `f (e i) (e j) = c` for all `i < j`. -/
def OrdPartition (α β γ : Ordinal) : Prop :=
  ∀ (f : OrdinalSet α → OrdinalSet α → Fin 2),
    (∃ e : OrdinalSet β ↪o OrdinalSet α,
      ∀ i j : OrdinalSet β, i < j → f (e i) (e j) = 0) ∨
    (∃ e : OrdinalSet γ ↪o OrdinalSet α,
      ∀ i j : OrdinalSet γ, i < j → f (e i) (e j) = 1)

/--
Erdős–Hajnal Conjecture on Partition Ordinals (Problem #118)
[Er87, Er90, Er95d, Er97f] — **DISPROVED**

An ordinal `α` is called a *partition ordinal* if `α → (α, 3)²`, i.e., every
2-coloring of pairs from a linearly ordered set of order type `α` contains either
a monochromatic copy of `α` in color 0 (red) or a monochromatic triangle K₃ in
color 1 (blue).

Erdős and Hajnal conjectured that for every partition ordinal `α` and every `n ≥ 3`,
we also have `α → (α, n)²`.

This conjecture is FALSE, as independently shown by Schipperus [Sc99] (published in
[Sc10]) and Darby [Da99]. For example, `ω^(ω^2)` is a partition ordinal, i.e.
`ω^(ω^2) → (ω^(ω^2), 3)²` holds (Schipperus [Sc10] and Darby, independently; Problem #591).
But Larson [La00] showed that `ω^(ω^2) → (ω^(ω^2), 5)²` fails.

See also Hajnal–Larson, Chapter 2.9 of [HST10] for background and proof sketches.
-/
theorem erdos_problem_118 :
    ¬ ∀ (α : Ordinal), OrdPartition α α 3 →
      ∀ n : ℕ, 3 ≤ n → OrdPartition α α (↑n) :=
  sorry

/--
`ω^(ω^2)` is a partition ordinal (PROVED; Schipperus [Sc10] and Darby, independently; Problem
#591): `ω^(ω^2) → (ω^(ω^2), 3)²`.
-/
theorem erdos_problem_118.variants.omega_omega_sq_partition :
    OrdPartition (ω ^ (ω ^ (2 : Ordinal))) (ω ^ (ω ^ (2 : Ordinal))) 3 :=
  sorry

/--
Larson [La00] (PROVED): `ω^(ω^2) ↛ (ω^(ω^2), 5)²`. Some 2-colouring of the pairs has neither a
red copy of `ω^(ω^2)` nor a blue K₅ (a "pentagram"). Together with the previous variant, this
witnesses `erdos_problem_118` with α = ω^(ω^2) and n = 5.
-/
theorem erdos_problem_118.variants.larson :
    ¬ OrdPartition (ω ^ (ω ^ (2 : Ordinal))) (ω ^ (ω ^ (2 : Ordinal))) 5 :=
  sorry
